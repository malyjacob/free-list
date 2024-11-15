module free_list;

import std.experimental.allocator.common;
import std.typecons : Flag, Yes, No;
import std.math.traits : isPowerOf2;

@safe @nogc nothrow pure
size_t roundUpToAlignment(size_t n, uint alignment) {
	assert(alignment.isPowerOf2);
	immutable uint slack = cast(uint) n & (alignment - 1);
	const result = slack ? n + alignment - slack : n;
	assert(result >= n);
	return result;
}

@nogc nothrow pure
void[] roundUpToAlignment(void[] b, uint a) {
	auto e = b.ptr + b.length;
	auto p = cast(void*) roundUpToAlignment(cast(size_t) b.ptr, a);
	if (e <= p)
		return null;
	return p[0 .. e - p];
}

struct FreeList(ParentAllocator,
	size_t minSize, size_t maxSize = minSize,
	Flag!"adaptive" adaptive = No.adaptive, uint theAlignment = platformAlignment) {
	import std.traits : hasMember;
	import std.typecons : Ternary;
	import std.math.traits;
	import std.algorithm.comparison : clamp;
	import std.algorithm.mutation : fill;
	static import std.algorithm.comparison;
	import core.stdc.string : memmove;

	// the node before the memory block that the allocator owns.
	// used for store the basic info of the relevant block.
	private struct Node {
		Node* next;
		// the exact size of the memory allocated by this allocator.
		size_t volum;
	}

	// the alignment of parent must be equal or greater than `theAlignment`.
	static assert(ParentAllocator.alignment >= theAlignment);
	// `theAlignment` must be equal or greater than `Node.align`, that is 8
	static assert(theAlignment >= Node.alignof);

	// the alignment default paltformAlignment
	alias alignment = theAlignment;

	static assert(maxSize >= alignment, "Maximum size must be equal or greater than its alignment.");
	static assert(minSize != unbounded, "Use minSize = 0 for no low bound.");

	static if (stateSize!ParentAllocator)
		ParentAllocator parent;
	else
		alias parent = ParentAllocator.instance;

	static if (minSize == chooseAtRuntime)
		private size_t _min = chooseAtRuntime;
	static if (maxSize == chooseAtRuntime)
		private size_t _max = chooseAtRuntime;

	// the head of the list that trace the allocated memory blocks.
	private Node* allocatedRoot;
	// the head of the list that trace the free memory blocks.
	// the free-list is self sorted from small to large
	private Node* freeRoot;

	static if (minSize == chooseAtRuntime) {
		@nogc nothrow @safe pure
		@property size_t min() const {
			assert(_min != chooseAtRuntime);
			return _min;
		}

		@nogc nothrow
		@property void min(size_t low) {
			// the `allocatedRoot` must be null.
			assert(allocatedRoot is null);
			assert(low <= _max || _max == chooseAtRuntime);
			minimize;
			_min = low;
		}
	}
	else {
		alias min = minSize;
	}

	static if (maxSize == chooseAtRuntime) {
		@nogc nothrow @safe pure
		@property size_t max() const {
			assert(_max != chooseAtRuntime);
			return _max;
		}

		@nogc nothrow
		@property void max(size_t high) {
			// the `allocatedRoot` must be null.
			assert(allocatedRoot is null);
			// `high` must be equal or greater than alignment.
			assert((high >= _min || _min == chooseAtRuntime)
					&& high >= alignment);
			minimize;
			_max = high;
		}
	}
	else {
		alias max = maxSize;
	}

	@system unittest {
		import std.experimental.allocator.common : chooseAtRuntime;
		import std.experimental.allocator.mallocator : Mallocator;

		FreeList!(Mallocator, chooseAtRuntime, chooseAtRuntime) a;

		a.min = 64;
		a.max = 128;
		assert(a.min == 64);
		assert(a.max == 128);
	}

	static if (maxSize != chooseAtRuntime) // prepare some block on free-list when initialized.
		this(size_t expectedInitialNum, size_t bytes = maxSize) nothrow {
			assert(expectedInitialNum != 0 && bytes > 0 && bytes != unbounded && bytes >= minSize);
			static if (maxSize != unbounded)
				assert(bytes == maxSize);
			auto aligned_node_size = Node.sizeof.roundUpToAlignment(alignment);
			auto required_allocates = goodAllocSize(bytes);
			void[] blk;
			foreach (_; 0 .. expectedInitialNum) {
				blk = parent.allocate(required_allocates + aligned_node_size);
				if (blk is null)
					return;
				Node* node = cast(Node*) blk.ptr;
				node.volum = blk.length - Node.sizeof;
				node.next = freeRoot;
				freeRoot = node;
			}
		}

	@nogc nothrow @safe pure
	private bool tooSmall(size_t n) const {
		static if (minSize == 0)
			return false;
		else
			return n < min;
	}

	@nogc nothrow @safe pure
	private bool tooLarge(size_t n) const {
		static if (maxSize == unbounded)
			return false;
		else
			return n > max;
	}

	// whether the size `n` is eligible.
	@nogc nothrow @safe pure
	private bool freeListEligible(size_t n) const {
		if (min == 0 && max == unbounded)
			return true;
		if (min == 0 && !n)
			return false;
		if (min == max)
			return n == max;
		else
			return !tooSmall(n) && !tooLarge(n);
	}

	// get the good size.
	@nogc nothrow @safe pure
	size_t goodAllocSize(size_t bytes) {
		assert(bytes);
		assert(!(min == chooseAtRuntime || max == chooseAtRuntime));
		if (!freeListEligible(bytes))
			return unbounded;
		if (max != unbounded)
			return max.roundUpToAlignment(alignment);
		return bytes.roundUpToAlignment(alignment);
	}

	static if (adaptive == Yes.adaptive) {
		// used for trimming the free-list if possible
		private int recentDeallocateNum = 0;

		// allocate extra memory blocks from parent at the head of free-list if possible
		nothrow private void updateStats(size_t requiredAllocates, uint a) {
			auto aligned_node_size = Node.sizeof.roundUpToAlignment(a);
			// if the block is within 1024 that parent would allocate, then the extra block num is 2,
			// else if the block is within 4096 that parent would allocate, then the extra block num is 1,
			// else no extra block that parent should allocate.
			immutable size_t extra_block_num = requiredAllocates < (1024 - aligned_node_size) ?
				2 : requiredAllocates < (4096 - aligned_node_size) ? 1 : 0;
			void[] blk;
			foreach (_; 0 .. extra_block_num) {
				if (a != alignment) {
					static if (hasMember!(ParentAllocator, "alignedAllocate"))
						blk = parent.alignedAllocate(aligned_node_size + requiredAllocates, a);
				}
				else
					blk = parent.allocate(requiredAllocates + aligned_node_size);
				if (blk is null)
					return;
				Node* node = cast(Node*) blk.ptr;
				node.volum = blk.length - Node.sizeof;
				node.next = freeRoot;
				freeRoot = node;
			}
		}

		// trim some blocks away from free-list if possible
		static if (hasMember!(ParentAllocator, "deallocate"))
			nothrow private void updateStats(Node* cur, Node* prev) {
				auto num = clamp(recentDeallocateNum - 1, 0, 8);
				prev = cur ? prev : null;
				cur = cur ? cur : freeRoot;
				while (cur && num) {
					auto target = cur;
					cur = cur.next;
					parent.deallocate(blockFor(target));
					--num;
				}
				prev ? (prev.next = cur) : (freeRoot = cur);
				recentDeallocateNum = 0;
			}
		else
			@nogc nothrow @safe pure
			private void updateStats(Node* cur, Node* prev) {
			}
	}

	// get the block allocated by parent
	@nogc nothrow @trusted pure
	private void[] blockFor(const Node* p) const {
		assert(p);
		return (cast(void*) p)[0 .. p.volum + Node.sizeof];
	}

	// get the relative node
	@nogc nothrow @trusted pure
	private inout(Node)* nodeFor(inout void* p) inout {
		if (!p)
			return null;
		auto cur = cast() allocatedRoot;
		while (cur) {
			auto pos = cast(size_t) p;
			auto bottom = (cast(size_t) cur + Node.sizeof).roundUpToAlignment(alignment);
			auto top = (cast(size_t) cur + Node.sizeof + cur.volum);
			if (pos >= bottom && pos < top)
				return cur;
			cur = cur.next;
		}
		return null;
	}

	// whether the block is owned by allocator
	@nogc nothrow @safe pure
	Ternary owns(const void[] b) const {
		return nodeFor(&b[0]) is null ? Ternary.no : Ternary.yes;
	}

	// resolve the internal pointer to the block that allocator owns.
	@nogc nothrow Ternary resolveInternalPointer(const void* p, ref void[] result) {
		return resolveInternalPointer(p, alignment, result);
	}

	// resolve the internal pointer to the block that allocator owns with alignment info.
	@nogc nothrow Ternary resolveInternalPointer(const void* p, uint a, ref void[] result) {
		assert(a >= alignment);
		auto node = nodeFor(p);
		if (!node)
			return Ternary.no;
		result = blockFor(node)[Node.sizeof .. $].roundUpToAlignment(a);
		return Ternary.yes;
	}

	// the inernal implement of allocate, allocateZeroed, alignedReallocate.
	// cut the block in specified size and return it.
	nothrow private void[] allocateEligible(string fillMode)(size_t bytes, uint a = cast(uint) alignment)
		if (fillMode == "void" || fillMode == "zero") {
		assert(a >= alignment && a.isPowerOf2);
		enum bool is_fill_zero = fillMode == "zero";
		static if (adaptive == Yes.adaptive) // used fot updateStats
			bool too_large;
		Node* cur = freeRoot, prev = null;
		auto required_allocates = goodAllocSize(bytes);
		// search the suitable block in free-list.
		// if there is a suitable block in free-list,
		// than allocate it and attatch the relevant node at the head of allocated-list.
		while (cur) {
			auto blk = blockFor(cur)[Node.sizeof .. $].roundUpToAlignment(a);
			if (blk.length < required_allocates) {
				prev = cur;
				cur = cur.next;
				continue;
			}
			// mark too_large true if the block's volum is more than double of required alllocated size.
			// this may triggle the trimming of free-list.
			static if (adaptive == Yes.adaptive) {
				if (cur.volum >= 2 * required_allocates) {
					too_large = true;
					break;
				}
			}
			prev ? (prev.next = cur.next) : (freeRoot = cur.next);
			cur.next = allocatedRoot;
			allocatedRoot = cur;
			return blk[0 .. bytes];
		}
		// if no suitable block in free-list, then fetch the memory block from parent.
		void[] blk;
		auto aligned_node_size = Node.sizeof.roundUpToAlignment(a);
		// if a is greater than alignment, then use parent's alignedAllocate to allocate
		if (a != alignment) {
			static if (hasMember!(ParentAllocator, "alignedAllocate"))
				blk = parent.alignedAllocate(aligned_node_size + required_allocates, a);
			else
				return null;
		}
		else
			blk = parent.allocate(required_allocates + aligned_node_size);
		if (blk is null)
			return null;
		static if (is_fill_zero) {
			auto tmp = cast(ubyte[]) blk;
			tmp.fill(cast(ubyte) 0);
		}
		// attach the relevant node at the head of allocated-list
		Node* node = cast(Node*) blk.ptr;
		node.volum = blk.length - Node.sizeof;
		node.next = allocatedRoot;
		allocatedRoot = node;
		static if (adaptive == Yes.adaptive) {
			if (too_large || (max != unbounded && !cur))
				updateStats(cur, prev);
			updateStats(required_allocates, a);
		}
		return blk[aligned_node_size .. aligned_node_size + bytes];
	}

	nothrow void[] allocate(size_t n) {
		if (freeListEligible(n))
			return allocateEligible!"void"(n);
		return null;
	}

	nothrow void[] allocateZeroed(size_t n) {
		if (freeListEligible(n))
			return allocateEligible!"zero"(n);
		return null;
	}

	// note: the a must be equal or greater than alignment
	static if (hasMember!(ParentAllocator, "alignedAllocate"))
		nothrow void[] alignedAllocate(size_t n, uint a) {
			assert(a >= alignment && isPowerOf2(a));
			if (freeListEligible(n))
				return allocateEligible!"void"(n, a);
			return null;
		}

	nothrow bool reallocate(ref void[] b, size_t s) {
		if (!b.ptr) {
			b = allocate(s);
			return b.length == s;
		}
		if (s == 0) {
			if (!deallocate(b))
				return false;
			b = null;
			return true;
		}
		if (b.length == s)
			return true;
		// if expand the block, then try to move the position of the block to match its alignment,
		// if not success, then allocate a new block and assign the orignal data to the new block. 
		else if (b.length < s) {
			if (alignedMove(b, s, alignment))
				return true;
			auto new_blk = allocate(s);
			if (new_blk.length != s)
				return false;
			new_blk[0 .. b.length] = b[];
			if (!deallocate(b))
				return false;
			b = new_blk;
			return true;
		}
		else {
			b = b[0 .. s];
			return true;
		}
	}

	static if (hasMember!(ParentAllocator, "alignedAllocate"))
		nothrow bool alignedReallocate(ref void[] b, size_t s, uint a) {
			assert(a >= alignment && isPowerOf2(a));
			// if the a is same as allocator's alignment, then redirect to `reallocate`.
			if (a == alignment)
				return reallocate(b, s);
			if (!b.ptr) {
				b = alignedAllocate(s, a);
				return b.length == s;
			}
			if (s == 0) {
				if (!deallocate(b))
					return false;
				b = null;
				return true;
			}
			// if `b` is not aligned to `a`, then jump to `LAlignedMoveOrAllocate`.
			if (cast(size_t) b.ptr % a != 0)
				goto LAlignedMoveOrAllocate;
			else {
				if (b.length == s)
					return true;
				else if (b.length < s)
					goto LAlignedMoveOrAllocate;
				else {
					b = b[0 .. s];
					return true;
				}
			}
		LAlignedMoveOrAllocate:
			auto result = alignedMove(b, s, a);
			if (result)
				return true;
			auto new_blk = alignedAllocate(s, a);
			if (new_blk.length != s)
				return false;
			if (b.length <= s)
				new_blk[0 .. b.length] = b[];
			else
				new_blk[] = b[0 .. s];
			if (!deallocate(b))
				return false;
			b = new_blk;
			return true;
		}

	@nogc nothrow bool expand(ref void[] b, size_t delta) {
		return alignedExpand(b, delta, alignment);
	}

	@nogc nothrow bool alignedExpand(ref void[] b, size_t delta, uint a) {
		assert(a >= alignment && isPowerOf2(a));
		return alignedMove(b, b.length + delta, a);
	}

	// the inner implement of alignedExpand, but this method can be used when shrinking the block,
	// which is useful in the implement of reallocate and alignedReallocate. 
	@nogc nothrow private bool alignedMove(ref void[] b, size_t s, uint a) {
		if (b is null || s == 0)
			return false;
		Node* node = nodeFor(b.ptr);
		if (!node)
			return false;
		void[] blk = blockFor(node);
		static if (hasMember!(ParentAllocator, "expand"))
			if ((b.length < s || a != alignment) && parent.expand(blk, s - b.length)) {
				// if expand from parent success, then update the value of `volum`
				node.volum = blk.length - Node.sizeof;
			}
		blk = roundUpToAlignment(blk[Node.sizeof .. $], a);
		if (blk is null)
			return false;
		b = memmove(blk.ptr, b.ptr, std.algorithm.comparison.min(b.length, s))[0 .. s];
		return true;
	}

	// deallocate the block and insert its relevant node into free-list according to the info of its relevant node
	@nogc nothrow bool deallocate(void[] b) {
		if (!b)
			return true;
		// search the relevant node on allocated-list to deallocate that is put
		// the block from allocated-list to free-list.
		// in fact, if the allocator is not unbouned, this searching operation is faster.
		Node* cur = allocatedRoot, prev;
		while (cur) {
			auto pos = cast(size_t) b.ptr;
			auto bottom = (cast(size_t) cur + Node.sizeof).roundUpToAlignment(alignment);
			auto top = (cast(size_t) cur + Node.sizeof + cur.volum);
			if (pos >= bottom && pos < top)
				break;
			prev = cur;
			cur = cur.next;
		}
		// if search succeed, then insert the node into free-list according its volum,
		// which would make the free-list sorted and would help allocator allocate blocks
		// in suitable size when the allocating request happens.
		if (cur) {
			prev ? (prev.next = cur.next) : (allocatedRoot = cur.next);
			auto target = cur;
			auto volum = target.volum;
			cur = freeRoot, prev = null;
			while (cur) {
				if (volum <= cur.volum)
					break;
				prev = cur;
				cur = cur.next;
			}
			target.next = cur;
			prev ? (prev.next = target) : (freeRoot = target);
			// record the times of deallocating until the next future allocating request happen.
			static if (adaptive == Yes.adaptive)
				++recentDeallocateNum;
			return true;
		}
		return false;
	}

	// deallocate all blocks traced by allocated-list,
	// and then insert their relevant nodes into free-list according to the info of their relevant node.
	// this method does actually not discard the blocks.
	@nogc nothrow bool deallocateAll() {
		Node* cur = freeRoot, prev = null;
		int num;
		while (allocatedRoot) {
			++num;
			while (cur) {
				if (allocatedRoot.volum <= cur.volum)
					break;
				prev = cur;
				cur = cur.next;
			}
			auto target = allocatedRoot;
			allocatedRoot = allocatedRoot.next;
			target.next = cur;
			prev ? (prev.next) = target : (freeRoot = target);
		}
		// record the times of deallocating until the next future allocating request happen.
		static if (adaptive == Yes.adaptive)
			recentDeallocateNum += num;
		return true;
	}

	// descard all blocks traced by allocated-list,
	// that is return the blocks managered by allocated-list to parent allocator.
	static if (hasMember!(ParentAllocator, "deallocate"))
		nothrow void release() {
			while (allocatedRoot) {
				auto blk = blockFor(allocatedRoot);
				allocatedRoot = allocatedRoot.next;
				parent.deallocate(blk);
			}
		}

	// discard all blocks traced by free-list,
	// that is return the blocks managered by free-list to parent allocator.
	static if (hasMember!(ParentAllocator, "deallocate"))
		nothrow void minimize() {
			while (freeRoot) {
				auto blk = blockFor(freeRoot);
				freeRoot = freeRoot.next;
				parent.deallocate(blk);
			}
		}

	// shrink the free-list manually.
	static if (hasMember!(ParentAllocator, "deallocate"))
		nothrow void shrink(size_t expectedNum) {
			assert(expectedNum != 0);
			while (freeRoot && expectedNum) {
				auto target = freeRoot;
				freeRoot = freeRoot.next;
				parent.deallocate(blockFor(target));
				--expectedNum;
			}
		}

	static if (hasMember!(ParentAllocator, "deallocate"))
		 ~this() {
			release();
			minimize();
		}
}

@system @nogc nothrow unittest {
	import std.experimental.allocator.common;
	import std.experimental.allocator.mallocator : AlignedMallocator;
	import std.typecons : Ternary, Flag, Yes, No;

	alias Alloc = FreeList!(AlignedMallocator, 0, platformAlignment, Yes.adaptive);
	Alloc fl;
	assert(fl.freeRoot is null);
	auto b1 = fl.allocate(1);
	assert(b1.length == 1);
	assert(fl.goodAllocSize(1) == fl.max);
	assert(fl.freeRoot !is null);
	assert(fl.freeRoot.next !is null);
	assert(fl.freeRoot.next.next is null);
	assert(fl.freeRoot.volum == platformAlignment);
	assert(fl.freeRoot.next.volum == platformAlignment);

	assert(fl.allocatedRoot !is null);
	assert(fl.allocatedRoot.next is null);
	assert(fl.allocatedRoot.volum == platformAlignment);
	assert(cast(void*) fl.allocatedRoot + fl.Node.sizeof.roundUpToAlignment(
			platformAlignment) == b1.ptr);

	// assert(!fl.expand(b1, 128));
	assert(fl.expand(b1, 13));
	assert(b1.length == 14);
	assert(fl.goodAllocSize(14) == fl.max);

	auto b2 = fl.allocate(4);
	assert(b2.length == 4);
	assert(fl.goodAllocSize(4) == fl.max);
	assert(fl.freeRoot.next is null);

	assert(fl.allocatedRoot.next !is null);
	assert(fl.allocatedRoot.volum == platformAlignment);
	assert(cast(void*) fl.allocatedRoot + fl.Node.sizeof.roundUpToAlignment(
			platformAlignment) == b2.ptr);

	auto b3 = fl.allocate(platformAlignment + 1);
	assert(b3 is null);

	assert(fl.owns(b1) == Ternary.yes && fl.owns(b2) == Ternary.yes);

	assert(fl.deallocate(b1));
	assert(fl.deallocate(b2));
	assert(fl.freeRoot.next.next !is null);
	assert(fl.allocatedRoot is null);
	assert(fl.recentDeallocateNum == 2);

	// this operation is more likely to invoke the adaptive functions
	b3 = fl.alignedAllocate(platformAlignment, 256);
	assert(b3 !is null);
	assert(b3.length == platformAlignment);
	assert(cast(size_t) b3.ptr % 256 == 0);

	fl.deallocate(b3);

	fl.shrink(1);
	fl.shrink(1024);
	assert(fl.freeRoot is null);

	fl.minimize;
	assert(fl.freeRoot is null);
}

@nogc @system nothrow unittest {
	import std.experimental.allocator.mallocator;
	import std.experimental.allocator.common;
	import std.typecons : Flag, Yes, No;

	alias Alloc = FreeList!(AlignedMallocator, 0, unbounded, Yes.adaptive);

	Alloc fl = Alloc(4, 32);
	assert(fl.freeRoot !is null);
	assert(fl.freeRoot.volum == 32);
	assert(fl.freeRoot.next.volum == 32);
	assert(fl.freeRoot.next.next.volum == 32);
	assert(fl.freeRoot.next.next.next.volum == 32);
	assert(fl.freeRoot.next.next.next.next is null);

	auto b1 = fl.allocateZeroed(32);
	auto b2 = fl.allocateZeroed(16);
	assert(b1.length == 32);
	assert(b2.length == 16);
	assert(fl.allocatedRoot !is null);
	assert(fl.allocatedRoot.next !is null);

	assert(fl.expand(b1, 0));
	// assert(!fl.expand(b1, 1));

	// this operation may invoke the adaptive functions
	assert(fl.reallocate(b1, 512));
	assert(b1.length == 512);

	// this operation may invoke the adaptive functions
	assert(fl.reallocate(b2, 72));
	assert(b2.length == 72);

	// this operation may invoke the adaptive functions
	assert(fl.alignedReallocate(b2, 72, 512));
	assert(b2.length == 72);

	fl.release;
	fl.shrink(1024);
	assert(fl.freeRoot is null);
	assert(fl.allocatedRoot is null);
}

// import std.experimental.allocator;
// import std.experimental.allocator.mallocator;
// import std.experimental.allocator.mmap_allocator;
// import std.experimental.allocator.building_blocks.bitmapped_block;
// import std.experimental.allocator.building_blocks.allocator_list;
// import std.experimental.allocator.building_blocks.segregator;
// import std.experimental.allocator.building_blocks.region;

// alias PageFreeList = FreeList!(MmapAllocator, 1 << 16, 1 << 17);
// alias BookMarkFreeList = FreeList!(Mallocator, 0, unbounded, Yes.adaptive);

// PageFreeList base_fl_alloc = void;
// BookMarkFreeList bkmk_alloc = void;

// static this() {
// 	base_fl_alloc = PageFreeList(4);
// 	bkmk_alloc = BookMarkFreeList();
// }

// alias Dele(size_t BlkSize) = n =>
// 	BitmappedBlock!(BlkSize, platformAlignment, PageFreeList*, No.multiblock)(
// 		&base_fl_alloc, (1 << 16));

// alias Alloc = Segregator!(
// 	16, AllocatorList!(Dele!16, BookMarkFreeList*),
// 	32, AllocatorList!(Dele!32, BookMarkFreeList*),
// 	64, AllocatorList!(Dele!64, BookMarkFreeList*),
// 	128, AllocatorList!(Dele!128, BookMarkFreeList*),
// 	256, FreeList!(Mallocator, 128, 256, Yes.adaptive),
// 	512, FreeList!(Mallocator, 256, 512, Yes.adaptive),
// 	4096, AllocatorList!(n => Region!(PageFreeList*)(&base_fl_alloc, 1 << 17), BookMarkFreeList*),
// 	MmapAllocator,
// );

// @system nothrow unittest {
// 	static void test() {
// 		Alloc alloc;
// 		alloc.allocatorForSize!(16).bkalloc = &bkmk_alloc;
// 		alloc.allocatorForSize!(32).bkalloc = &bkmk_alloc;
// 		alloc.allocatorForSize!(64).bkalloc = &bkmk_alloc;
// 		alloc.allocatorForSize!(128).bkalloc = &bkmk_alloc;
// 		alloc.allocatorForSize!(1024).bkalloc = &bkmk_alloc;

// 		alloc.allocate(12);
// 		alloc.allocate(30);
// 		alloc.allocate(48);
// 		alloc.allocate(100);
// 		alloc.allocate(144);
// 		alloc.allocate(288);
// 		alloc.allocate(625);
// 		alloc.allocate(1 << 11);
// 	}

// 	test();
// }

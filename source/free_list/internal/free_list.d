module free_list.internal.free_list;

import std.experimental.allocator.common : platformAlignment, stateSize,
    chooseAtRuntime, unbounded;
import std.typecons : Flag, Yes, No, Ternary;
import std.math.traits : isPowerOf2;
import std.traits : hasMember;
import std.algorithm.mutation : fill;
import core.stdc.string : memmove;
import core.atomic : atomicOp, cas, atomicStore, atomicLoad;
import core.internal.spinlock : SpinLock;
static import std.algorithm.comparison;
import free_list.internal.util;

struct FreeList(ParentAllocator, size_t minSize, size_t maxSize = minSize,
    uint maxCacheSize = 16, uint theAlignment = platformAlignment)
{
    private struct Node
    {
        Node* next;
        uint volum;
        uint affinity = 3;
    }

    static assert(ParentAllocator.alignment >= theAlignment);
    static assert(theAlignment >= Node.alignof);
    static assert(maxCacheSize > 0);

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

    private Node* allocatedRoot;
    private Node* freeRoot;
    private Node* cacheRoot;

    private uint cacheNum;
    private uint refineFactor;

    private uint _baseAffinity = 3;

    private uint _appendNum = 2;

    static if (minSize != chooseAtRuntime && maxSize != chooseAtRuntime)
        this(size_t num) nothrow
        {
            assert(num);
            auto aligned_node_size = Node.sizeof.roundUpToAlignment(alignment);
            auto required_size = maxSize.roundUpToAlignment(alignment);
            void[] blk;
            Node* targetRoot;
            foreach (_; 0 .. num)
                {
                blk = parent.allocate(required_size + aligned_node_size);
                if (blk is null)
                    throw badAllocationError();
                Node* node = cast(Node*) blk.ptr;
                node.volum = cast(uint)(blk.length - Node.sizeof);
                node.affinity = 3;
                node.next = targetRoot, targetRoot = node;
            }

            freeRoot = targetRoot;
        }

    @nogc nothrow @safe pure @property uint baseAffinity() const
    {
        return _baseAffinity;
    }

    @nogc nothrow @safe pure @property void baseAffinity(uint affinity)
    {
        _baseAffinity = affinity;
    }

    @nogc nothrow @safe pure @property uint appendNum() const
    {
        return _appendNum;
    }

    @nogc nothrow @safe pure @property void appendNum(uint apNum)
    {
        _appendNum = apNum;
    }

    static if (minSize == chooseAtRuntime)
    {
        @nogc nothrow @safe pure @property size_t min() const
        {
            assert(_min != chooseAtRuntime);
            return _min;
        }

        @nogc nothrow @safe pure @property void min(size_t low)
        {
            assert(allocatedRoot is null);
            assert(cacheRoot is null);
            assert(freeRoot is null);
            assert(low <= _max || _max == chooseAtRuntime);
            _min = low;
        }
    }
    else
    {
        alias min = minSize;
    }

    static if (maxSize == chooseAtRuntime)
    {
        @nogc nothrow @safe pure @property size_t max() const
        {
            assert(_max != chooseAtRuntime);
            return _max;
        }

        @nogc nothrow @property void max(size_t high)
        {
            assert(allocatedRoot is null);
            assert(cacheRoot is null);
            assert(freeRoot is null);
            assert((high >= _min || _min == chooseAtRuntime) && high >= alignment);
            _max = high;
        }
    }
    else
    {
        alias max = maxSize;
    }

    static if (minSize == chooseAtRuntime && maxSize == chooseAtRuntime)
    {
        @nogc nothrow @safe pure void setBounds(size_t low, size_t high)
        {
            assert(low <= high && high >= (void*).sizeof);
            assert(_min == chooseAtRuntime || _max == chooseAtRuntime);
            _min = low, _max = high;
        }
    }

    @nogc nothrow @safe pure private bool tooSmall(size_t n) const
    {
        static if (minSize == 0)
            return false;
        else
            return n < min;
    }

    @nogc nothrow @safe pure private bool tooLarge(size_t n) const
    {
        static if (maxSize == unbounded)
            return false;
        else
            return n > max;
    }

    @nogc nothrow @safe pure private bool freeListEligible(size_t n) const
    {
        if (min == 0 && max == unbounded)
            return true;
        if (min == 0 && !n)
            return false;
        if (min == max)
            return n == max;
        else
            return !tooSmall(n) && !tooLarge(n);
    }

    @nogc nothrow @safe pure size_t goodAllocSize(size_t bytes) const
    {
        assert(bytes);
        assert(!(min == chooseAtRuntime || max == chooseAtRuntime));
        if (!freeListEligible(bytes))
            return unbounded;
        if (max != unbounded)
            return max.roundUpToAlignment(alignment);
        return bytes.roundUpToAlignment(alignment);
    }

    @nogc nothrow @trusted pure private void[] blockFor(const Node* p) const
    {
        assert(p);
        return (cast(void*) p)[0 .. p.volum + Node.sizeof];
    }

    @nogc nothrow @trusted pure private Node* nodeFor(const void* p)
    {
        if (!p)
            return null;
        auto cur = allocatedRoot;
        while (cur)
        {
            auto pos = cast(size_t) p;
            auto bottom = (cast(size_t) cur + Node.sizeof).roundUpToAlignment(alignment);
            auto top = (cast(size_t) cur + Node.sizeof + cur.volum);
            if (pos >= bottom && pos < top)
                return cur;
            cur = cur.next;
        }
        return null;
    }

    @nogc nothrow @safe pure Ternary owns(const void[] b)
    {
        return nodeFor(&b[0]) is null ? Ternary.no : Ternary.yes;
    }

    @nogc nothrow @safe Ternary resolveInternalPointer(const void* p, ref void[] result)
    {
        return resolveInternalPointer(p, alignment, result);
    }

    @nogc nothrow @trusted Ternary resolveInternalPointer(const void* p, uint a, ref void[] result)
    {
        assert(a >= alignment);
        auto node = nodeFor(p);
        if (!node)
            return Ternary.no;
        result = blockFor(node)[Node.sizeof .. $].roundUpToAlignment(a);
        return Ternary.yes;
    }

    nothrow private void refineFree()
    {
        Node* cur = freeRoot, prev = null, targetRoot = null;
        while (cur)
        {
            if (cur.affinity == 0 || --cur.affinity == 0)
            {
                auto target = cur;
                cur = cur.next;
                prev ? (prev.next = cur) : (freeRoot = cur);
                target.next = targetRoot, targetRoot = target;
            }
            else
                prev = cur, cur = cur.next;
        }
        refineFactor = 0;
        while (targetRoot)
        {
            auto next = targetRoot.next;
            if (parent.deallocate(blockFor(targetRoot)))
                targetRoot = next;
            else
                throw badDeallocationError();
        }
    }

    nothrow private Node* fetchFromParent(size_t requiredAllocates, uint a)
    {
        auto aligned_node_size = Node.sizeof.roundUpToAlignment(a);
        void[] blk;
        Node* targetRoot, result;
        foreach (idx; 0 .. appendNum + 1)
        {
            if (a != alignment)
            {
                static if (hasMember!(ParentAllocator, "alignedAllocate"))
                    blk = parent.alignedAllocate(aligned_node_size + requiredAllocates, a);
            }
            else
                blk = parent.allocate(requiredAllocates + aligned_node_size);
            if (blk is null)
                throw badAllocationError();
            Node* node = cast(Node*) blk.ptr;
            node.volum = cast(uint)(blk.length - Node.sizeof);
            node.affinity = baseAffinity();
            if (idx == 0)
                result = node;
            else
                node.next = targetRoot, targetRoot = node;
        }
        while (targetRoot)
        {
            auto next = targetRoot.next;
            Node* cur = freeRoot, prev = null;
            while (cur)
            {
                if (targetRoot.volum <= cur.volum)
                    break;
                prev = cur, cur = cur.next;
            }
            targetRoot.next = cur;
            prev ? (prev.next = targetRoot) : (freeRoot = targetRoot);
            targetRoot = next;
        }
        return result;
    }

    nothrow private void[] allocateEligible(size_t bytes, uint a = cast(uint) alignment)
    {
        assert(a >= alignment && a.isPowerOf2);
        auto required_allocates = goodAllocSize(bytes);
        Node* cur = freeRoot, prev = null;
        while (cur)
        {
            auto blk = blockFor(cur)[Node.sizeof .. $].roundUpToAlignment(a);
            if (blk.length < required_allocates)
            {
                prev = cur, cur = cur.next;
                continue;
            }
            if (cur.volum >= 2 * required_allocates)
                break;
            prev ? (prev.next = cur.next) : (freeRoot = cur.next);
            cur.next = allocatedRoot;
            allocatedRoot = cur;
            return blk[0 .. bytes];
        }
        auto cache_list_old = cacheRoot;
        auto cach_list_num = cacheNum;
        cacheRoot = null;
        cacheNum = 0;
        if (++refineFactor + cach_list_num >= maxCacheSize)
            refineFree();
        Node* target_node;
        while (cache_list_old)
        {
            auto blk = blockFor(cache_list_old)[Node.sizeof .. $].roundUpToAlignment(a);
            auto next = cache_list_old.next;
            if (blk.length < required_allocates
                || cache_list_old.volum >= 2 * required_allocates || target_node !is null)
            {
                auto volum = cache_list_old.volum;
                cur = freeRoot, prev = null;
                while (cur)
                {
                    if (volum <= cur.volum)
                        break;
                    prev = cur, cur = cur.next;
                }
                cache_list_old.next = cur;
                prev ? (prev.next = cache_list_old) : (freeRoot = cache_list_old);
            }
            else
                target_node = cache_list_old;
            cache_list_old = next;
        }
        if (target_node)
        {
            target_node.next = allocatedRoot;
            allocatedRoot = target_node;
            return blockFor(target_node)[Node.sizeof .. $].roundUpToAlignment(a)[0 .. bytes];
        }
        auto node = fetchFromParent(required_allocates, a);
        node.next = allocatedRoot;
        allocatedRoot = node;
        return blockFor(node)[Node.sizeof .. $].roundUpToAlignment(a)[0 .. bytes];
    }

    nothrow void[] allocate(size_t n)
    {
        if (freeListEligible(n))
            return allocateEligible(n);
        return null;
    }

    nothrow void[] allocateZeroed(size_t n)
    {
        if (freeListEligible(n))
        {
            auto tmp = cast(ubyte[]) allocateEligible(n);
            tmp.fill(cast(ubyte) 0);
            return cast(void[]) tmp;
        }
        return null;
    }

    static if (hasMember!(ParentAllocator, "alignedAllocate"))
        nothrow void[] alignedAllocate(size_t n, uint a)
        {
            assert(a >= alignment && isPowerOf2(a));
            if (freeListEligible(n))
                return allocateEligible(n, a);
            return null;
        }

    static if (hasMember!(ParentAllocator, "alignedAllocate"))
        nothrow void[] alignedAllocateZeroed(size_t n, uint a)
        {
            assert(a >= alignment && isPowerOf2(a));
            if (freeListEligible(n))
                {
                auto tmp = cast(ubyte[]) allocateEligible(n, a);
                tmp.fill(cast(ubyte) 0);
                return cast(void[]) tmp;
            }
            return null;
        }

    nothrow bool reallocate(ref void[] b, size_t s)
    {
        if (!b.ptr)
        {
            b = allocate(s);
            return b.length == s;
        }
        if (s == 0)
        {
            if (!deallocate(b))
                return false;
            b = null;
            return true;
        }
        if (b.length == s)
            return true;
        else if (b.length < s)
        {
            if (alignedMove(b, s, alignment))
                return true;
            if (!deallocate(b))
                return false;
            auto new_blk = allocate(s);
            if (new_blk.length != s)
                return false;
            new_blk[0 .. b.length] = b[];
            b = new_blk;
            return true;
        }
        else
        {
            b = b[0 .. s];
            return true;
        }
    }

    static if (hasMember!(ParentAllocator, "alignedAllocate"))
        nothrow bool alignedReallocate(ref void[] b, size_t s, uint a)
        {
            assert(a >= alignment && isPowerOf2(a));
            if (a == alignment)
                return reallocate(b, s);
            if (!b.ptr)
                {
                b = alignedAllocate(s, a);
                return b.length == s;
            }
            if (s == 0)
                {
                if (!deallocate(b))
                    return false;
                b = null;
                return true;
            }
            if (cast(size_t) b.ptr % a != 0)
                goto LAlignedMoveOrAllocate;
            else
                {
                if (b.length == s)
                    return true;
                else if (b.length < s)
                    goto LAlignedMoveOrAllocate;
                else
                    {
                    b = b[0 .. s];
                    return true;
                }
            }
        LAlignedMoveOrAllocate:
            if (alignedMove(b, s, a))
                return true;
            if (!deallocate(b))
                return false;
            auto new_blk = alignedAllocate(s, a);
            if (new_blk.length != s)
                return false;
            if (b.length <= s)
                new_blk[0 .. b.length] = b[];
            else
                new_blk[] = b[0 .. s];
            b = new_blk;
            return true;
        }

    nothrow bool expand(ref void[] b, size_t delta)
    {
        return alignedExpand(b, delta, alignment);
    }

    nothrow bool alignedExpand(ref void[] b, size_t delta, uint a)
    {
        assert(a >= alignment && isPowerOf2(a));
        return alignedMove(b, b.length + delta, a);
    }

    nothrow private bool alignedMove(ref void[] b, size_t s, uint a)
    {
        if (b is null || s == 0)
            return false;
        Node* node = nodeFor(b.ptr);
        if (!node)
            return false;
        void[] blk = blockFor(node);
        static if (hasMember!(ParentAllocator, "expand"))
            if (b.length < s && parent.expand(blk, s - b.length))
                {
                node.volum = cast(uint)(blk.length - Node.sizeof);
            }
        blk = roundUpToAlignment(blk[Node.sizeof .. $], a);
        if (blk is null || blk.length < s)
            return false;
        b = memmove(blk.ptr, b.ptr, std.algorithm.comparison.min(b.length, s))[0 .. s];
        return true;
    }

    nothrow bool deallocate(void[] b, Flag!"release" release = No.release)
    {
        if (!b)
            return true;
        Node* cur = allocatedRoot, prev;
        while (cur)
        {
            auto pos = cast(size_t) b.ptr;
            auto bottom = (cast(size_t) cur + Node.sizeof).roundUpToAlignment(alignment);
            auto top = (cast(size_t) cur + Node.sizeof + cur.volum);
            if (pos >= bottom && pos < top)
                break;
            prev = cur, cur = cur.next;
        }
        if (cur)
            prev ? (prev.next = cur.next) : (allocatedRoot = cur.next);
        else
            return false;
        static if (hasMember!(ParentAllocator, "deallocate"))
            if (release == Yes.release)
                {
                if (!parent.deallocate(blockFor(cur)))
                    throw badDeallocationError();
                return true;
            }
        cur.affinity = baseAffinity();
        Node* cache_list_old;
        cur.next = cacheRoot;
        cacheRoot = cur;
        if (++cacheNum >= maxCacheSize)
        {
            cache_list_old = cacheRoot;
            cacheRoot = null;
            cacheNum = 0;
        }
        if (cache_list_old is null)
            return true;
        refineFree();
        cur = null, prev = null;
        while (cache_list_old)
        {
            auto next = cache_list_old.next;
            auto volum = cache_list_old.volum;
            cur = freeRoot, prev = null;
            while (cur)
            {
                if (volum <= cur.volum)
                    break;
                prev = cur, cur = cur.next;
            }
            cache_list_old.next = cur;
            prev ? (prev.next = cache_list_old) : (freeRoot = cache_list_old);
            cache_list_old = next;
        }
        return true;
    }

    nothrow bool deallocateAll(Flag!"release" release = No.release)
    {
        auto targetRoot = allocatedRoot;
        allocatedRoot = null;
        static if (hasMember!(ParentAllocator, "deallocate"))
        {
            if (release == Yes.release)
            {
                while (targetRoot)
                {
                    auto next = targetRoot.next;
                    if (parent.deallocate(blockFor(targetRoot)))
                        targetRoot = next;
                    else
                        throw badDeallocationError();
                }
                return true;
            }
        }
        refineFree();
        Node* cur, prev;
        while (targetRoot)
        {
            auto next = targetRoot.next;
            auto volum = targetRoot.volum;
            targetRoot.affinity = baseAffinity();
            cur = freeRoot, prev = null;
            while (cur)
            {
                if (volum <= cur.volum)
                    break;
                prev = cur, cur = cur.next;
            }
            targetRoot.next = cur;
            prev ? (prev.next = targetRoot) : (freeRoot = targetRoot);
            targetRoot = next;
        }
        return true;
    }

    static if (hasMember!(ParentAllocator, "deallocate"))
    {
        nothrow void release()
        {
            deallocateAll(Yes.release);
        }

        nothrow void minimize()
        {
            auto targetRoot = freeRoot;
            freeRoot = null;
            refineFactor = 0;
            while (targetRoot)
            {
                auto next = targetRoot.next;
                if (parent.deallocate(blockFor(targetRoot)))
                    targetRoot = next;
                else
                    throw badDeallocationError();
            }
            targetRoot = cacheRoot;
            cacheRoot = null;
            cacheNum = 0;
            while (targetRoot)
            {
                auto next = targetRoot.next;
                if (parent.deallocate(blockFor(targetRoot)))
                    targetRoot = next;
                else
                    throw badDeallocationError();
            }
        }

        ~this() @trusted nothrow
        {
            release();
            minimize();
        }
    }
}

shared struct SharedFreelist(ParentAllocator, size_t minSize, size_t maxSize = minSize,
    uint maxCacheSize = 16, uint theAlignment = platformAlignment)
{
    private shared struct Node
    {
        Node* next;
        uint volum;
        uint affinity = 3;
    }

    static assert(ParentAllocator.alignment >= theAlignment);
    static assert(theAlignment >= Node.alignof);
    static assert(maxCacheSize > 0);

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

    private Node* allocatedRoot;
    private Node* freeRoot;
    private Node* cacheRoot;

    private SpinLock allocatedLock;
    private SpinLock freeLock;
    private SpinLock cacheLock;

    private uint cacheNum;
    private uint refineFactor;

    private uint _baseAffinity = 3;

    private uint _appendNum = 2;

    static if (minSize != chooseAtRuntime && maxSize != chooseAtRuntime)
        this(size_t num) nothrow
        {
            assert(num);
            auto aligned_node_size = Node.sizeof.roundUpToAlignment(alignment);
            auto required_size = maxSize.roundUpToAlignment(alignment);
            void[] blk;
            Node* targetRoot;
            foreach (_; 0 .. num)
                {
                blk = parent.allocate(required_size + aligned_node_size);
                if (blk is null)
                    throw badAllocationError();
                Node* node = cast(Node*) blk.ptr;
                node.volum = cast(uint)(blk.length - Node.sizeof);
                node.affinity = 3;
                node.next = targetRoot, targetRoot = node;
            }
            freeRoot = targetRoot;
        }

    @nogc nothrow @safe pure @property uint baseAffinity() const
    {
        return atomicLoad(_baseAffinity);
    }

    @nogc nothrow @safe pure @property void baseAffinity(uint affinity)
    {
        atomicStore(_baseAffinity, affinity);
    }

    @nogc nothrow @safe pure @property uint appendNum() const
    {
        return atomicLoad(_appendNum);
    }

    @nogc nothrow @safe pure @property void appendNum(uint apNum)
    {
        atomicStore(_appendNum, apNum);
    }

    static if (minSize == chooseAtRuntime)
    {
        @nogc nothrow @safe pure @property size_t min() const
        {
            assert(_min != chooseAtRuntime);
            return _min;
        }

        @nogc nothrow @safe pure @property void min(size_t low)
        {
            assert(allocatedRoot is null);
            assert(cacheRoot is null);
            assert(freeRoot is null);
            assert(low <= _max || _max == chooseAtRuntime);
            _min = low;
        }
    }
    else
    {
        alias min = minSize;
    }

    static if (maxSize == chooseAtRuntime)
    {
        @nogc nothrow @safe pure @property size_t max() const
        {
            assert(_max != chooseAtRuntime);
            return _max;
        }

        @nogc nothrow @safe pure @property void max(size_t high)
        {
            assert(allocatedRoot is null);
            assert(cacheRoot is null);
            assert(freeRoot is null);
            assert((high >= _min || _min == chooseAtRuntime) && high >= alignment);
            _max = high;
        }
    }
    else
    {
        alias max = maxSize;
    }

    static if (minSize == chooseAtRuntime && maxSize == chooseAtRuntime)
    {
        @nogc nothrow @safe void setBounds(size_t low, size_t high)
        {
            if (!(low <= high && high >= (void*).sizeof))
                throw badAllocationError(
                    "low must be lower than high, high must at least 1 pointer size");
            if (_min != chooseAtRuntime)
                throw badAllocationError("SharedFreeList.min must be initialized exactly once.");
            if (_max != chooseAtRuntime)
                throw badAllocationError("SharedFreeList.max must be initialized exactly once.");
            _min = low, _max = high;
        }
    }

    @nogc nothrow @safe pure private bool tooSmall(size_t n) const
    {
        static if (minSize == 0)
            return false;
        else
            return n < min;
    }

    @nogc nothrow @safe pure private bool tooLarge(size_t n) const
    {
        static if (maxSize == unbounded)
            return false;
        else
            return n > max;
    }

    @nogc nothrow @safe pure private bool freeListEligible(size_t n) const
    {
        if (min == 0 && max == unbounded)
            return true;
        if (min == 0 && !n)
            return false;
        if (min == max)
            return n == max;
        else
            return !tooSmall(n) && !tooLarge(n);
    }

    @nogc nothrow @safe pure size_t goodAllocSize(size_t bytes) const
    {
        assert(bytes);
        assert(!(min == chooseAtRuntime || max == chooseAtRuntime));
        if (!freeListEligible(bytes))
            return unbounded;
        if (max != unbounded)
            return max.roundUpToAlignment(alignment);
        return bytes.roundUpToAlignment(alignment);
    }

    @nogc nothrow @trusted pure private void[] blockFor(const Node* p) const
    {
        assert(p);
        return (cast(void*) p)[0 .. p.volum + Node.sizeof];
    }

    @nogc nothrow @trusted private Node* nodeFor(Flag!"withlock" withlock = Yes.withlock)(
        const void* p)
    {
        if (!p)
            return null;
        static if (withlock == Yes.withlock)
            allocatedLock.lock();
        shared cur = cast() allocatedRoot;
        while (cur)
        {
            auto pos = cast(size_t) p;
            auto bottom = (cast(size_t) cur + Node.sizeof).roundUpToAlignment(alignment);
            auto top = (cast(size_t) cur + Node.sizeof + cur.volum);
            if (pos >= bottom && pos < top)
            {
                static if (withlock == Yes.withlock)
                    allocatedLock.unlock();
                return cur;
            }
            cur = cur.next;
        }
        static if (withlock == Yes.withlock)
            allocatedLock.unlock();
        return null;
    }

    @nogc nothrow @safe Ternary owns(const void[] b)
    {
        return nodeFor(&b[0]) is null ? Ternary.no : Ternary.yes;
    }

    @nogc nothrow @safe Ternary resolveInternalPointer(const void* p, ref void[] result)
    {
        return resolveInternalPointer(p, alignment, result);
    }

    @nogc nothrow @trusted Ternary resolveInternalPointer(const void* p, uint a, ref void[] result)
    {
        assert(a >= alignment);
        allocatedLock.lock();
        auto node = nodeFor!(No.withlock)(p);
        if (!node)
        {
            allocatedLock.unlock();
            return Ternary.no;
        }
        result = blockFor(node)[Node.sizeof .. $].roundUpToAlignment(a);
        allocatedLock.unlock();
        return Ternary.yes;
    }

    nothrow private void refineFree()
    {
        freeLock.lock();
        Node* cur = freeRoot, prev = null, targetRoot = null;
        while (cur)
        {
            if (cur.affinity == 0 || atomicOp!"-="((*cur).affinity, 1) == 0)
            {
                auto target = cur;
                cur = cur.next;
                prev ? (prev.next = cur) : (freeRoot = cur);
                target.next = targetRoot, targetRoot = target;
            }
            else
                prev = cur, cur = cur.next;
        }
        atomicStore(refineFactor, 0);
        freeLock.unlock();
        while (targetRoot)
        {
            auto next = targetRoot.next;
            if (parent.deallocate(blockFor(targetRoot)))
                targetRoot = next;
            else
                throw badDeallocationError();
        }
    }

    nothrow private Node* fetchFromParent(size_t requiredAllocates, uint a)
    {
        auto aligned_node_size = Node.sizeof.roundUpToAlignment(a);
        void[] blk;
        Node* targetRoot, result;
        foreach (idx; 0 .. appendNum + 1)
        {
            if (a != alignment)
            {
                static if (hasMember!(ParentAllocator, "alignedAllocate"))
                    blk = parent.alignedAllocate(aligned_node_size + requiredAllocates, a);
            }
            else
                blk = parent.allocate(requiredAllocates + aligned_node_size);
            if (blk is null)
                throw badAllocationError();
            Node* node = cast(Node*) blk.ptr;
            node.volum = cast(uint)(blk.length - Node.sizeof);
            node.affinity = baseAffinity();
            if (idx == 0)
                result = node;
            else
                node.next = targetRoot, targetRoot = node;
        }
        freeLock.lock();
        while (targetRoot)
        {
            auto next = targetRoot.next;
            Node* cur = freeRoot, prev = null;
            while (cur)
            {
                if (targetRoot.volum <= cur.volum)
                    break;
                prev = cur, cur = cur.next;
            }
            targetRoot.next = cur;
            prev ? (prev.next = targetRoot) : (freeRoot = targetRoot);
            targetRoot = next;
        }
        freeLock.unlock();
        return result;
    }

    nothrow private void[] allocateEligible(size_t bytes, uint a = cast(uint) alignment)
    {
        assert(a >= alignment && a.isPowerOf2);
        auto required_allocates = goodAllocSize(bytes);
        freeLock.lock();
        Node* cur = freeRoot, prev = null;
        while (cur)
        {
            auto blk = blockFor(cur)[Node.sizeof .. $].roundUpToAlignment(a);
            if (blk.length < required_allocates)
            {
                prev = cur, cur = cur.next;
                continue;
            }
            if (cur.volum >= 2 * required_allocates)
                break;
            prev ? (prev.next = cur.next) : (freeRoot = cur.next);
            freeLock.unlock();
            allocatedLock.lock();
            cur.next = allocatedRoot;
            allocatedRoot = cur;
            allocatedLock.unlock();
            return blk[0 .. bytes];
        }
        freeLock.unlock();
        cacheLock.lock();
        auto cache_list_old = cacheRoot;
        auto cache_list_num = cacheNum;
        cacheRoot = null;
        cacheNum = 0;
        cacheLock.unlock();
        if (atomicOp!"+="(refineFactor, 1) + cache_list_num >= maxCacheSize)
            refineFree();
        Node* target_node;
        freeLock.lock();
        while (cache_list_old)
        {
            auto blk = blockFor(cache_list_old)[Node.sizeof .. $].roundUpToAlignment(a);
            auto next = cache_list_old.next;
            if (blk.length < required_allocates
                || cache_list_old.volum >= 2 * required_allocates || target_node !is null)
            {
                auto volum = cache_list_old.volum;
                cur = freeRoot, prev = null;
                while (cur)
                {
                    if (volum <= cur.volum)
                        break;
                    prev = cur, cur = cur.next;
                }
                cache_list_old.next = cur;
                prev ? (prev.next = cache_list_old) : (freeRoot = cache_list_old);
            }
            else
                target_node = cache_list_old;
            cache_list_old = next;
        }
        freeLock.unlock();
        if (target_node)
        {
            allocatedLock.lock();
            target_node.next = allocatedRoot;
            allocatedRoot = target_node;
            allocatedLock.unlock();
            return blockFor(target_node)[Node.sizeof .. $].roundUpToAlignment(a)[0 .. bytes];
        }
        auto node = fetchFromParent(required_allocates, a);
        allocatedLock.lock();
        node.next = allocatedRoot;
        allocatedRoot = node;
        allocatedLock.unlock();
        return blockFor(node)[Node.sizeof .. $].roundUpToAlignment(a)[0 .. bytes];
    }

    nothrow void[] allocate(size_t n)
    {
        if (freeListEligible(n))
            return allocateEligible(n);
        return null;
    }

    nothrow void[] allocateZeroed(size_t n)
    {
        if (freeListEligible(n))
        {
            auto tmp = cast(ubyte[]) allocateEligible(n);
            tmp.fill(cast(ubyte) 0);
            return cast(void[]) tmp;
        }
        return null;
    }

    static if (hasMember!(ParentAllocator, "alignedAllocate"))
        nothrow void[] alignedAllocate(size_t n, uint a)
        {
            assert(a >= alignment && isPowerOf2(a));
            if (freeListEligible(n))
                return allocateEligible(n, a);
            return null;
        }

    static if (hasMember!(ParentAllocator, "alignedAllocate"))
        nothrow void[] alignedAllocateZeroed(size_t n, uint a)
        {
            assert(a >= alignment && isPowerOf2(a));
            if (freeListEligible(n))
                {
                auto tmp = cast(ubyte[]) allocateEligible(n, a);
                tmp.fill(cast(ubyte) 0);
                return cast(void[]) tmp;
            }
            return null;
        }

    nothrow bool reallocate(ref void[] b, size_t s)
    {
        if (!b.ptr)
        {
            b = allocate(s);
            return b.length == s;
        }
        if (s == 0)
        {
            if (!deallocate(b))
                return false;
            b = null;
            return true;
        }
        if (b.length == s)
            return true;
        else if (b.length < s)
        {
            if (alignedMove(b, s, alignment))
                return true;
            if (!deallocate(b))
                return false;
            auto new_blk = allocate(s);
            if (new_blk.length != s)
                return false;
            new_blk[0 .. b.length] = b[];
            b = new_blk;
            return true;
        }
        else
        {
            b = b[0 .. s];
            return true;
        }
    }

    static if (hasMember!(ParentAllocator, "alignedAllocate"))
        nothrow bool alignedReallocate(ref void[] b, size_t s, uint a)
        {
            assert(a >= alignment && isPowerOf2(a));
            if (a == alignment)
                return reallocate(b, s);
            if (!b.ptr)
                {
                b = alignedAllocate(s, a);
                return b.length == s;
            }
            if (s == 0)
                {
                if (!deallocate(b))
                    return false;
                b = null;
                return true;
            }
            if (cast(size_t) b.ptr % a != 0)
                goto LAlignedMoveOrAllocate;
            else
                {
                if (b.length == s)
                    return true;
                else if (b.length < s)
                    goto LAlignedMoveOrAllocate;
                else
                    {
                    b = b[0 .. s];
                    return true;
                }
            }
        LAlignedMoveOrAllocate:
            if (alignedMove(b, s, a))
                return true;
            if (!deallocate(b))
                return false;
            auto new_blk = alignedAllocate(s, a);
            if (new_blk.length != s)
                return false;
            if (b.length <= s)
                new_blk[0 .. b.length] = b[];
            else
                new_blk[] = b[0 .. s];
            b = new_blk;
            return true;
        }

    nothrow bool expand(ref void[] b, size_t delta)
    {
        return alignedExpand(b, delta, alignment);
    }

    nothrow bool alignedExpand(ref void[] b, size_t delta, uint a)
    {
        assert(a >= alignment && isPowerOf2(a));
        return alignedMove(b, b.length + delta, a);
    }

    nothrow private bool alignedMove(ref void[] b, size_t s, uint a)
    {
        if (b is null || s == 0)
            return false;
        allocatedLock.lock();
        Node* node = nodeFor!(No.withlock)(b.ptr);
        if (!node)
        {
            allocatedLock.unlock();
            return false;
        }
        void[] blk = blockFor(node);
        static if (hasMember!(ParentAllocator, "expand"))
            if (b.length < s && parent.expand(blk, s - b.length))
                {
                node.volum = cast(uint)(blk.length - Node.sizeof);
            }
        blk = roundUpToAlignment(blk[Node.sizeof .. $], a);
        if (blk is null || blk.length < s)
        {
            allocatedLock.unlock();
            return false;
        }
        b = memmove(blk.ptr, b.ptr, std.algorithm.comparison.min(b.length, s))[0 .. s];
        allocatedLock.unlock();
        return true;
    }

    nothrow bool deallocate(void[] b, Flag!"release" release = No.release)
    {
        if (!b)
            return true;
        allocatedLock.lock();
        Node* cur = allocatedRoot, prev;
        while (cur)
        {
            auto pos = cast(size_t) b.ptr;
            auto bottom = (cast(size_t) cur + Node.sizeof).roundUpToAlignment(alignment);
            auto top = (cast(size_t) cur + Node.sizeof + cur.volum);
            if (pos >= bottom && pos < top)
                break;
            prev = cur, cur = cur.next;
        }
        if (cur)
            prev ? (prev.next = cur.next) : (allocatedRoot = cur.next);
        else
        {
            allocatedLock.unlock();
            return false;
        }
        allocatedLock.unlock();
        static if (hasMember!(ParentAllocator, "deallocate"))
            if (release == Yes.release)
                {
                if (!parent.deallocate(blockFor(cur)))
                    throw badDeallocationError();
                return true;
            }
        cur.affinity = baseAffinity();
        Node* cache_list_old;
        cacheLock.lock();
        cur.next = cacheRoot;
        cacheRoot = cur;
        if (atomicOp!"+="(cacheNum, 1) >= maxCacheSize)
        {
            cache_list_old = cacheRoot;
            cacheRoot = null;
            cacheNum = 0;
        }
        cacheLock.unlock();
        if (cache_list_old is null)
            return true;
        refineFree();
        cur = null, prev = null;
        freeLock.lock();
        while (cache_list_old)
        {
            auto next = cache_list_old.next;
            auto volum = cache_list_old.volum;
            cur = freeRoot, prev = null;
            while (cur)
            {
                if (volum <= cur.volum)
                    break;
                prev = cur, cur = cur.next;
            }
            cache_list_old.next = cur;
            prev ? (prev.next = cache_list_old) : (freeRoot = cache_list_old);
            cache_list_old = next;
        }
        freeLock.unlock();
        return true;
    }

    nothrow bool deallocateAll(Flag!"release" release = No.release)
    {
        allocatedLock.lock();
        auto targetRoot = allocatedRoot;
        allocatedRoot = null;
        allocatedLock.unlock();
        static if (hasMember!(ParentAllocator, "deallocate"))
        {
            if (release == Yes.release)
            {
                while (targetRoot)
                {
                    auto next = targetRoot.next;
                    if (parent.deallocate(blockFor(targetRoot)))
                        targetRoot = next;
                    else
                        throw badDeallocationError();
                }
                return true;
            }
        }
        refineFree();
        Node* cur, prev;
        while (targetRoot)
        {
            auto next = targetRoot.next;
            auto volum = targetRoot.volum;
            targetRoot.affinity = baseAffinity();
            freeLock.lock();
            cur = freeRoot, prev = null;
            while (cur)
            {
                if (volum <= cur.volum)
                    break;
                prev = cur, cur = cur.next;
            }
            targetRoot.next = cur;
            prev ? (prev.next = targetRoot) : (freeRoot = targetRoot);
            freeLock.unlock();
            targetRoot = next;
        }
        return true;
    }

    static if (hasMember!(ParentAllocator, "deallocate"))
        nothrow void release()
        {
            deallocateAll(Yes.release);
        }

    static if (hasMember!(ParentAllocator, "deallocate"))
        nothrow void minimize()
        {
            freeLock.lock();
            auto targetRoot = freeRoot;
            freeRoot = null;
            atomicStore(refineFactor, 0);
            freeLock.unlock();
            while (targetRoot)
                {
                auto next = targetRoot.next;
                if (parent.deallocate(blockFor(targetRoot)))
                    targetRoot = next;
                else
                    throw badDeallocationError();
            }
            cacheLock.lock();
            targetRoot = cacheRoot;
            cacheRoot = null;
            cacheNum = 0;
            cacheLock.unlock();
            while (targetRoot)
                {
                auto next = targetRoot.next;
                if (parent.deallocate(blockFor(targetRoot)))
                    targetRoot = next;
                else
                    throw badDeallocationError();
            }
        }

    static if (hasMember!(ParentAllocator, "deallocate"))
         ~this() @trusted nothrow
        {
            release();
            minimize();
        }
}

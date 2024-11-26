module free_list.internal.n_free_list_lite;

import std.experimental.allocator.common : platformAlignment, stateSize,
    unbounded, chooseAtRuntime;
import std.experimental.allocator : makeArray, dispose;
import std.experimental.allocator.mallocator;
import std.typecons : Flag, Yes, No, Ternary;
import std.math.traits : isPowerOf2;
import std.traits : hasMember;
import std.algorithm.mutation : fill, swap;
import core.atomic : atomicOp, cas, atomicStore, atomicLoad;
import object : hashOf;
import free_list.internal.util;

shared struct NSharedFreeListLite(ParentAllocator, size_t minSize, size_t maxSize = minSize,
    size_t allocatedSlotNum = 8, uint theAlignment = platformAlignment)
{
    private shared struct Node
    {
        Node* next;
    }

    static assert(ParentAllocator.alignment >= theAlignment);
    static assert(theAlignment >= Node.alignof && theAlignment.isPowerOf2);
    static assert(allocatedSlotNum > 0);

    alias alignment = theAlignment;

    static assert(maxSize >= alignment, "Maximum size must be equal or greater than its alignment.");
    static assert(maxSize >= minSize,
        "Maximum size must be equal or greater than its Minimum size.");

    private shared align(64) struct AllocatedSlot
    {
        Node* allocatedRoot;
        Node* allocatedTail;
        size_t allocatedNum;
        SpinLock allocatedLock;
    }

    static assert(AllocatedSlot.sizeof == 64);

    private uint _cacheLimit = 32;
    private uint _appendNum = 2;

    static if (minSize == chooseAtRuntime)
        private size_t _min = chooseAtRuntime;
    static if (maxSize == chooseAtRuntime)
        private size_t _max = chooseAtRuntime;
    static if (allocatedSlotNum == chooseAtRuntime)
        private AllocatedSlot[] _allocatedSlots;

    private align(64) uint cacheNum;

    private align(64) uint freeNum;

    private align(64) Node* freeRoot;
    private align(64) Node* cacheRoot;

    private align(64) SpinLock freeLock;
    private align(64) SpinLock cacheLock;
    static if (stateSize!ParentAllocator)
        align(64) ParentAllocator parent;
    else
        alias parent = ParentAllocator.instance;

    static if (allocatedSlotNum != chooseAtRuntime)
        private align(64) AllocatedSlot[allocatedSlotNum] _allocatedSlots;

    static if (minSize != chooseAtRuntime && maxSize != chooseAtRuntime)
        this(size_t num) nothrow
        {
            assert(num);
            auto aligned_node_size = Node.sizeof.roundUpToAlignment(alignment);
            auto required_size = maxSize.roundUpToAlignment(alignment);
            void[] blk;
            Node* targetRoot;
            foreach (i; 0 .. num)
                {
                blk = parent.allocate(required_size + aligned_node_size);
                if (blk is null)
                    throw badAllocationError();
                Node* node = cast(Node*) blk.ptr;
                node.next = targetRoot, targetRoot = node;
            }
            freeRoot = targetRoot;
            atomicOp!"+="(freeNum, cast(uint) num);
        }

    @nogc nothrow @safe pure @property uint appendNum() const
    {
        return atomicLoad(_appendNum);
    }

    @nogc nothrow @safe pure @property void appendNum(uint apNum)
    {
        atomicStore(_appendNum, apNum);
    }

    @nogc nothrow @safe pure @property uint cacheLimit() const
    {
        return atomicLoad(_cacheLimit);
    }

    @nogc nothrow @safe pure @property void cacheLimit(uint limit)
    {
        atomicStore(_cacheLimit, limit);
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

    static if (allocatedSlotNum == chooseAtRuntime)
    {
        @nogc nothrow void initAllocatedSlots(size_t slotNum)
        {
            _allocatedSlots = cast(AllocatedSlot[]) AlignedMallocator.instance.alignedAllocate(slotNum * AllocatedSlot.sizeof, 64);
            if (_allocatedSlots is null)
                throw badAllocationError("no more memory from AlignedMallocator to be allocated");
            import core.lifetime;
            foreach (i; 0 .. _allocatedSlots.length)
                emplace(&_allocatedSlots[i]);
        }
    }

    @nogc nothrow @safe pure private bool freeListEligible(size_t n) const
    {
        if (min == 0 && !n)
            return false;
        if (min == max)
            return n == max;
        else
            return n >= min && n <= max;
    }

    @nogc nothrow @safe pure size_t goodAllocSize(size_t bytes) const
    {
        assert(bytes);
        assert(!(min == chooseAtRuntime || max == chooseAtRuntime));
        if (!freeListEligible(bytes))
            return unbounded;
        return max.roundUpToAlignment(alignment);
    }

    pragma(inline, true) @nogc nothrow @trusted pure private void[] blockFor(const Node* p) const
    {
        assert(p);
        assert(!(min == chooseAtRuntime || max == chooseAtRuntime));
        auto aligned_node_size = Node.sizeof.roundUpToAlignment(alignment);
        auto required_size = max.roundUpToAlignment(alignment);
        return (cast(void*) p)[0 .. aligned_node_size + required_size];
    }

    pragma(inline, true) @nogc nothrow @safe private size_t getNodeIndex() const
    {
        return getThisThreadId.hashOf(1_000_000_000_000_002_481) % _allocatedSlots.length;
    }

    pragma(inline, true) @nogc nothrow @safe private ref AllocatedSlot allocatedSlot()
    {
        static if (allocatedSlotNum == chooseAtRuntime)
            assert(_allocatedSlots);
        return _allocatedSlots[getNodeIndex()];
    }

    pragma(inline, true) @nogc nothrow @safe private ref SpinLock allocatedLock()
    {
        static if (allocatedSlotNum == chooseAtRuntime)
            assert(_allocatedSlots);
        return _allocatedSlots[getNodeIndex()].allocatedLock;
    }

    pragma(inline, true) @nogc nothrow @trusted private Node* nodeFor(
        Flag!"withlock" withlock = Yes.withlock)(const void* p)
    {
        if (!p)
            return null;
        static if (withlock == Yes.withlock)
        {
            auto allocLock = &allocatedLock();
            allocLock.lock();
        }
        auto cur = allocatedSlot.allocatedRoot;
        while (cur)
        {
            auto pos = cast(size_t) p;
            auto bottom = (cast(size_t) cur + Node.sizeof).roundUpToAlignment(alignment);
            auto top = bottom + max.roundUpToAlignment(alignment);
            if (pos >= bottom && pos < top)
            {
                static if (withlock == Yes.withlock)
                    allocLock.unlock();
                return cur;
            }
            cur = cur.next;
        }
        static if (withlock == Yes.withlock)
            allocLock.unlock();
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

    pragma(inline, true) @nogc nothrow @trusted private Ternary resolveInternalPointer(
        const void* p, uint a, ref void[] result)
    {
        assert(a >= alignment);
        auto allocLock = &allocatedLock();
        allocLock.lock();
        auto node = nodeFor!(No.withlock)(p);
        if (!node)
        {
            allocLock.unlock();
            return Ternary.no;
        }
        result = blockFor(node)[Node.sizeof .. $].roundUpToAlignment(a);
        allocLock.unlock();
        return Ternary.yes;
    }

    nothrow private Node* fetchFromParent(size_t requiredAllocates)
    {
        auto aligned_node_size = Node.sizeof.roundUpToAlignment(alignment);
        void[] blk;
        Node* targetRoot, targetTail, result;
        auto num = appendNum;
        foreach (idx; 0 .. num + 1)
        {
            blk = parent.allocate(requiredAllocates + aligned_node_size);
            if (blk is null)
                throw badAllocationError();
            Node* node = cast(Node*) blk.ptr;
            if (idx == 0)
                result = node;
            else
            {
                node.next = targetRoot;
                if (targetRoot is null)
                    targetTail = node;
                targetRoot = node;
            }
        }
        if (targetRoot)
        {
            freeLock.lock();
            targetTail.next = freeRoot;
            freeRoot = targetRoot;
            atomicOp!"+="(this.freeNum, num);
            freeLock.unlock();
        }
        return result;
    }

    nothrow private void[] allocateEligible(size_t bytes)
    {
        auto required_allocates = goodAllocSize(bytes);
        Node* target;
        freeLock.lock();
        target = freeRoot;
        if (target)
        {
            freeRoot = freeRoot.next;
            atomicOp!"-="(this.freeNum, 1);
            freeLock.unlock();
            goto LIntoAllocatedList;
        }
        freeLock.unlock();
        cacheLock.lock();
        target = cacheRoot;
        if (target)
        {
            freeLock.lock();
            if (freeRoot !is null)
                freeLock.unlock();
            else
            {
                freeRoot = cacheRoot.next;
                freeNum = cacheNum - 1;
                freeLock.unlock();
                cacheRoot = null;
                cacheNum = 0;
                cacheLock.unlock();
                goto LIntoAllocatedList;
            }
        }
        cacheLock.unlock();
        target = fetchFromParent(required_allocates);
    LIntoAllocatedList:
        auto allocLock = &allocatedLock();
        allocLock.lock();
        auto slot = &allocatedSlot();
        target.next = slot.allocatedRoot;
        if (slot.allocatedRoot is null)
            slot.allocatedTail = target;
        slot.allocatedRoot = target;
        atomicOp!"+="(slot.allocatedNum, 1);
        allocLock.unlock();
        return blockFor(target)[Node.sizeof .. $].roundUpToAlignment(alignment)[0 .. bytes];
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

    @nogc nothrow bool expand(ref void[] b, size_t delta)
    {
        Node* node = nodeFor(b.ptr);
        if (node is null)
        {
            return false;
        }
        if (delta == 0)
            return true;
        void[] blk = blockFor(node)[Node.sizeof .. $].roundUpToAlignment(alignment);
        auto required_size = b.length + delta;
        if (blk.length < required_size)
            return false;
        b = blk[0 .. required_size];
        return true;
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
            if (expand(b, s - b.length))
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

    nothrow bool deallocate(void[] b, Flag!"release" release = No.release)
    {
        if (!b)
            return true;
        auto allocLock = &allocatedLock();
        allocLock.lock();
        auto slot = &allocatedSlot();
        Node* cur = slot.allocatedRoot, prev;
        while (cur)
        {
            if (cast(size_t) cur == (cast(size_t) b.ptr - Node.sizeof.roundUpToAlignment(alignment)))
                break;
            prev = cur, cur = cur.next;
        }
        if (cur)
        {
            prev ? (prev.next = cur.next) : (slot.allocatedRoot = cur.next);
            if (cur.next is null)
            {
                slot.allocatedTail = prev;
                if (slot.allocatedTail)
                    slot.allocatedTail.next = null;
            }
            atomicOp!"-="(slot.allocatedNum, 1);
        }
        else
        {
            allocLock.unlock();
            return false;
        }
        allocLock.unlock();
        static if (hasMember!(ParentAllocator, "deallocate"))
            if (release == Yes.release)
                {
                if (!parent.deallocate(blockFor(cur)))
                    throw badDeallocationError();
                return true;
            }
        cacheLock.lock();
        cur.next = cacheRoot;
        cacheRoot = cur;
        if (atomicOp!"+="(this.cacheNum, 1) >= cacheLimit)
        {
            freeLock.lock();
            Node* free_list_old = freeRoot;
            freeRoot = cacheRoot;
            freeNum = cacheNum;
            freeLock.unlock();
            cacheRoot = null;
            cacheNum = 0;
            cacheLock.unlock();
            while (free_list_old)
            {
                auto next = free_list_old.next;
                if (!parent.deallocate(blockFor(free_list_old)))
                    throw badDeallocationError();
                free_list_old = next;
            }
        }
        else
            cacheLock.unlock();
        return true;
    }

    nothrow bool deallocateAll(Flag!"release" release = No.release)
    {
        auto allocLock = &allocatedLock();
        allocLock.lock();
        auto slot = &allocatedSlot();
        auto targetRoot = slot.allocatedRoot;
        auto targetTail = slot.allocatedTail;
        slot.allocatedRoot = null;
        slot.allocatedTail = null;
        slot.allocatedNum = 0;
        allocLock.unlock();
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
        if (targetRoot is null)
            return true;
        freeLock.lock();
        targetTail.next = freeRoot;
        freeRoot = targetRoot;
        freeLock.unlock();
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
            freeLock.lock();
            auto targetRoot = freeRoot;
            freeRoot = null;
            freeNum = 0;
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

        ~this() @trusted nothrow
        {
            minimize();
            foreach (ref slot; _allocatedSlots)
            {
                auto targetRoot = slot.allocatedRoot;
                while (targetRoot)
                {
                    auto next = targetRoot.next;
                    if (parent.deallocate(blockFor(targetRoot)))
                        targetRoot = next;
                    else
                        throw badDeallocationError();
                }
            }
            static if (allocatedSlotNum == chooseAtRuntime)
                AlignedMallocator.instance.deallocate(cast(void[]) _allocatedSlots);
        }
    }
}

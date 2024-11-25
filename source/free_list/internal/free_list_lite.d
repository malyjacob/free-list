module free_list.internal.free_list_lite;

import std.experimental.allocator.common : platformAlignment, stateSize,
    unbounded, chooseAtRuntime;
import std.typecons : Flag, Yes, No, Ternary;
import std.math.traits : isPowerOf2;
import std.traits : hasMember;
import std.algorithm.mutation : fill, swap;
import core.atomic : atomicOp, cas, atomicStore, atomicLoad;
import core.internal.spinlock : SpinLock;
import free_list.internal.util;

struct FreeListLite(ParentAllocator, size_t minSize, size_t maxSize = minSize,
    uint maxCacheSize = 16, uint theAlignment = platformAlignment)
{
    private struct Node
    {
        Node* next;
    }

    static assert(ParentAllocator.alignment >= theAlignment);
    static assert(theAlignment >= Node.alignof && theAlignment.isPowerOf2);
    static assert(maxCacheSize > 0);

    alias alignment = theAlignment;

    static assert(maxSize >= alignment, "Maximum size must be equal or greater than its alignment.");
    static assert(maxSize >= minSize,
        "Maximum size must be equal or greater than its Minimum size.");

    static if (stateSize!ParentAllocator)
        ParentAllocator parent;
    else
        alias parent = ParentAllocator.instance;

    static if (minSize == chooseAtRuntime)
        private size_t _min = chooseAtRuntime;
    static if (maxSize == chooseAtRuntime)
        private size_t _max = chooseAtRuntime;

    private Node* allocatedRoot;
    private Node* allocatedTail;

    private Node* freeRoot;
    private Node* cacheRoot;

    private uint allocatedNum;
    private uint freeNum;
    private uint cacheNum;

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
                node.next = targetRoot, targetRoot = node;
            }
            freeRoot = targetRoot;
            freeNum += cast(uint) num;
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

    @nogc nothrow @trusted pure private void[] blockFor(const Node* p) const
    {
        assert(p);
        assert(!(min == chooseAtRuntime || max == chooseAtRuntime));
        auto aligned_node_size = Node.sizeof.roundUpToAlignment(alignment);
        auto required_size = max.roundUpToAlignment(alignment);
        return (cast(void*) p)[0 .. aligned_node_size + required_size];
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
            auto top = bottom + max.roundUpToAlignment(alignment);
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

    @nogc nothrow @trusted private Ternary resolveInternalPointer(const void* p,
        uint a, ref void[] result)
    {
        assert(a >= alignment);
        auto node = nodeFor(p);
        if (!node)
        {
            return Ternary.no;
        }
        result = blockFor(node)[Node.sizeof .. $].roundUpToAlignment(a);
        return Ternary.yes;
    }

    nothrow private Node* fetchFromParent(size_t requiredAllocates)
    {
        auto aligned_node_size = Node.sizeof.roundUpToAlignment(alignment);
        void[] blk;
        Node* targetRoot, result;
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
                node.next = targetRoot, targetRoot = node;
        }
        freeRoot = targetRoot;
        freeNum += num;
        return result;
    }

    nothrow private void[] allocateEligible(size_t bytes)
    {
        auto required_allocates = goodAllocSize(bytes);
        Node* target;
        target = freeRoot;
        if (target)
        {
            freeRoot = freeRoot.next;
            --freeNum;
            goto LIntoAllocatedList;
        }
        target = cacheRoot;
        if (target)
        {
            freeRoot = cacheRoot.next;
            freeNum = cacheNum - 1;
            cacheRoot = null;
            cacheNum = 0;
            goto LIntoAllocatedList;
        }
        target = fetchFromParent(required_allocates);
    LIntoAllocatedList:
        target.next = allocatedRoot;
        if (allocatedRoot is null)
            allocatedTail = target;
        allocatedRoot = target;
        ++allocatedNum;
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
            return false;
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
        Node* cur = allocatedRoot, prev;
        while (cur)
        {
            if (cast(size_t) cur == (cast(size_t) b.ptr - Node.sizeof.roundUpToAlignment(alignment)))
                break;
            prev = cur, cur = cur.next;
        }
        if (cur)
        {
            prev ? (prev.next = cur.next) : (allocatedRoot = cur.next);
            if (cur.next is null)
            {
                assert(cur is allocatedTail);
                allocatedTail = prev;
                if (allocatedTail)
                    allocatedTail.next = null;
                else
                    assert(allocatedRoot is null);
            }
            --allocatedNum;
        }
        else
            return false;
        static if (hasMember!(ParentAllocator, "deallocate"))
            if (release == Yes.release)
                {
                if (!parent.deallocate(blockFor(cur)))
                    throw badDeallocationError();
                return true;
            }
        cur.next = cacheRoot;
        cacheRoot = cur;
        if (++cacheNum >= maxCacheSize)
        {
            swap(freeRoot, cacheRoot);
            swap(freeNum, cacheNum);
            uint dele_num = (cacheNum > maxCacheSize / 2) ? cacheNum - maxCacheSize / 2 : 0;
            while (dele_num && cacheRoot)
            {
                auto next = cacheRoot.next;
                if (!parent.deallocate(blockFor(cacheRoot)))
                    throw badDeallocationError();
                --dele_num;
                cacheRoot = next;
            }
            cacheNum -= dele_num;
        }
        return true;
    }

    nothrow bool deallocateAll(Flag!"release" release = No.release)
    {
        auto targetRoot = allocatedRoot;
        auto targetTail = allocatedTail;
        allocatedRoot = null;
        allocatedTail = null;
        allocatedNum = 0;
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
        targetTail.next = freeRoot;
        freeRoot = targetRoot;
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
            freeNum = 0;
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

shared struct SharedFreeListLite(ParentAllocator, size_t minSize,
    size_t maxSize = minSize, uint maxCacheSize = 16, uint theAlignment = platformAlignment)
{
    private shared struct Node
    {
        Node* next;
    }

    static assert(ParentAllocator.alignment >= theAlignment);
    static assert(theAlignment >= Node.alignof && theAlignment.isPowerOf2);
    static assert(maxCacheSize > 0);

    alias alignment = theAlignment;

    static assert(maxSize >= alignment, "Maximum size must be equal or greater than its alignment.");
    static assert(maxSize >= minSize,
        "Maximum size must be equal or greater than its Minimum size.");

    static if (stateSize!ParentAllocator)
        ParentAllocator parent;
    else
        alias parent = ParentAllocator.instance;

    static if (minSize == chooseAtRuntime)
        private size_t _min = chooseAtRuntime;
    static if (maxSize == chooseAtRuntime)
        private size_t _max = chooseAtRuntime;

    private Node* allocatedRoot;
    private Node* allocatedTail;
    private uint allocatedNum;
    private SpinLock allocatedLock;

    private Node* freeRoot;
    private uint freeNum;
    private SpinLock freeLock;

    private Node* cacheRoot;
    private uint cacheNum;
    private SpinLock cacheLock;

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

    @nogc nothrow @trusted pure private void[] blockFor(const Node* p) const
    {
        assert(p);
        assert(!(min == chooseAtRuntime || max == chooseAtRuntime));
        auto aligned_node_size = Node.sizeof.roundUpToAlignment(alignment);
        auto required_size = max.roundUpToAlignment(alignment);
        return (cast(void*) p)[0 .. aligned_node_size + required_size];
    }

    @nogc nothrow @trusted private Node* nodeFor(Flag!"withlock" withlock = Yes.withlock)(
        const void* p)
    {
        if (!p)
            return null;
        static if (withlock == Yes.withlock)
            allocatedLock.lock();
        auto cur = allocatedRoot;
        while (cur)
        {
            auto pos = cast(size_t) p;
            auto bottom = (cast(size_t) cur + Node.sizeof).roundUpToAlignment(alignment);
            auto top = bottom + max.roundUpToAlignment(alignment);
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

    @nogc nothrow @trusted private Ternary resolveInternalPointer(const void* p,
        uint a, ref void[] result)
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
        allocatedLock.lock();
        target.next = allocatedRoot;
        if (allocatedRoot is null)
            allocatedTail = target;
        allocatedRoot = target;
        atomicOp!"+="(this.allocatedNum, 1);
        allocatedLock.unlock();
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
        allocatedLock.lock();
        Node* cur = allocatedRoot, prev;
        while (cur)
        {
            if (cast(size_t) cur == (cast(size_t) b.ptr - Node.sizeof.roundUpToAlignment(alignment)))
                break;
            prev = cur, cur = cur.next;
        }
        if (cur)
        {
            prev ? (prev.next = cur.next) : (allocatedRoot = cur.next);
            if (cur.next is null)
            {
                allocatedTail = prev;
                if (allocatedTail)
                    allocatedTail.next = null;
            }
            atomicOp!"-="(this.allocatedNum, 1);
        }
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
        cacheLock.lock();
        cur.next = cacheRoot;
        cacheRoot = cur;
        if (atomicOp!"+="(this.cacheNum, 1) >= maxCacheSize)
        {
            freeLock.lock();
            swap(freeRoot, cacheRoot);
            swap(freeNum, cacheNum);
            freeLock.unlock();
            uint dele_num = (cacheNum > maxCacheSize / 2) ? cacheNum - maxCacheSize / 2 : 0;
            Node* dele_list;
            if (dele_num)
            {
                size_t i;
                while (i < dele_num && cacheRoot)
                {
                    auto next = cacheRoot.next;
                    cacheRoot.next = dele_list;
                    dele_list = cacheRoot;
                    cacheRoot = next;
                    ++i;
                }
                atomicOp!"-="(this.cacheNum, i);
            }
            cacheLock.unlock();
            while (dele_list)
            {
                auto next = dele_list.next;
                if (!parent.deallocate(blockFor(dele_list)))
                    throw badDeallocationError();
                dele_list = next;
            }
        }
        else
            cacheLock.unlock();
        return true;
    }

    nothrow bool deallocateAll(Flag!"release" release = No.release)
    {
        allocatedLock.lock();
        auto targetRoot = allocatedRoot;
        auto targetTail = allocatedTail;
        allocatedRoot = null;
        allocatedTail = null;
        allocatedNum = 0;
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
            release();
            minimize();
        }
    }
}

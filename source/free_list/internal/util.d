module free_list.internal.util;

import object : Error;
import core.lifetime : emplace;
import std.math.traits : isPowerOf2;
import core.atomic, core.thread;

@safe @nogc nothrow pure size_t roundUpToAlignment(size_t n, uint alignment)
{
    assert(alignment.isPowerOf2);
    immutable uint slack = cast(uint) n & (alignment - 1);
    const result = slack ? n + alignment - slack : n;
    assert(result >= n);
    return result;
}

@trusted @nogc nothrow pure void[] roundUpToAlignment(void[] b, uint a)
{
    auto e = b.ptr + b.length;
    auto p = cast(void*) roundUpToAlignment(cast(size_t) b.ptr, a);
    if (e <= p)
        return null;
    return p[0 .. e - p];
}

class BadAllocationError : Error
{
    this(string msg = "bad allocation from parent", Throwable nextInChain = null) pure nothrow @nogc @safe
    {
        super(msg, nextInChain);
    }
}

class BadDeallocationError : Error
{
    this(string msg = "bad deallocation from parent", Throwable nextInChain = null) pure nothrow @nogc @safe
    {
        super(msg, nextInChain);
    }
}

nothrow @nogc @trusted BadAllocationError badAllocationError(string msg = "")
{
    static void[__traits(classInstanceSize, BadAllocationError)] buffer;
    return msg.length ? emplace!BadAllocationError(buffer[0 .. $],
        msg) : emplace!BadAllocationError(buffer[0 .. $]);

}

nothrow @nogc @trusted BadDeallocationError badDeallocationError(string msg = "")
{
    static void[__traits(classInstanceSize, BadDeallocationError)] buffer;
    return msg.length ? emplace!BadDeallocationError(buffer[0 .. $],
        msg) : emplace!BadDeallocationError(buffer[0 .. $]);
}

version (Windows)
{
    import core.sys.windows.windows : GetCurrentThreadId;

    size_t getThisThreadId() nothrow @nogc @trusted
    {
        return cast(size_t) GetCurrentThreadId();
    }
}

version (Posix)
{
    import core.sys.posix.pthread : pthread_self;

    size_t getThisThreadId() nothrow @nogc @trusted
    {
        return cast(size_t) pthread_self();
    }
}

package shared struct SpinLock
{
@nogc nothrow:
    this(Contention contention) @trusted
    {
        this.contention = contention;
    }

    void yield(size_t k) @trusted
    {
        if (k < pauseThresh)
            return core.atomic.pause();
        else
            return Thread.yield();
    }

    void lock() @trusted
    {
        if (cas(&val, size_t(0), size_t(1)))
            return;
        immutable step = 1 << contention;
        while (true)
        {
            for (size_t n; atomicLoad!(MemoryOrder.raw)(val); n += step)
                yield(n);
            if (cas(&val, size_t(0), size_t(1)))
                return;
        }
    }

    void unlock() @trusted
    {
        atomicStore!(MemoryOrder.rel)(val, size_t(0));
    }

    size_t val;
    Contention contention = Contention.Medium;
}

package enum Contention : size_t
{
    Brief,
    Medium,
    Lengthy
}

private enum pauseThresh = 16;
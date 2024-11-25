import std.experimental.allocator;
import std.experimental.allocator.mallocator;
import std.experimental.allocator.gc_allocator;
import std.experimental.allocator.common;
import std.concurrency;
import core.thread;
import core.lifetime : moveEmplace;
import std.random;
import std.datetime;
import std.datetime.stopwatch : StopWatch;
import std.stdio;
import cmdline;

import free_list.internal.free_list : FreeList, SharedFreelist;
import free_list.internal.free_list_lite : FreeListLite, SharedFreeListLite;
import free_list.internal.n_free_list_lite : NSharedFreelistLite;
import free_list.internal.util : getThisThreadId;

alias Alloc = FreeList!(Mallocator, chooseAtRuntime, chooseAtRuntime, 32);
alias SharedAlloc = SharedFreelist!(Mallocator, 128, 1024, 32);

alias AllocLite = FreeListLite!(Mallocator, chooseAtRuntime, chooseAtRuntime, 32);
alias SharedAllocLite = SharedFreeListLite!(Mallocator, 128, 1024, 32);

alias NSharedAlocLite = NSharedFreelistLite!(Mallocator, 128, 1024, chooseAtRuntime);

void test_alloc(Allocator)(Allocator* ptr_alloc, size_t circle, size_t slot)
{
	enum size_t bottom = 256;
	enum size_t top = 1025;
	auto thread_num = getThisThreadId();
	auto hash_idx = thread_num.hashOf(1_000_000_000_000_002_481) % slot;
	writefln("this thread number is %s, the hash index is: %s", thread_num, hash_idx);
	auto ptr_arr = cast(void[][]) ptr_alloc.allocate(10 * (void[]).sizeof);
	foreach (i; 0 .. circle * 100)
	{
		auto idx = i % 10;
		size_t size = uniform(bottom, top);
		auto tmp = ptr_alloc.allocate(size);
		assert(tmp);
		ptr_arr[idx] = tmp;
		Thread.yield;
		if (idx == 9)
		{
			foreach (ele; ptr_arr)
				ptr_alloc.deallocate(ele);
		}
	}
	ptr_alloc.deallocate(cast(void[]) ptr_arr);
}

void test(Allocator)(Allocator* ptr_alloc, StopWatch* sw, size_t circle, size_t thnum, size_t slots = 8)
{
	sw.start();
	foreach (_; 0 .. thnum)
	{
		spawn(&test_alloc!Allocator, ptr_alloc, circle, slots);
	}

	thread_joinAll();
	sw.stop();
	writeln("Elapsed time: ", sw.peek().total!"msecs", " msecs");
}

@cmdline struct App
{
	mixin BEGIN;

	mixin DEF_BOOL_OPT!("lite", "-l", Desc_d!"choose the lite one of shared free list");
	mixin DEF_BOOL_OPT!("nonLite", "-n", Desc_d!"choose the non-lite one of shared free list");
	mixin DEF_BOOL_OPT!("newLite", "-m", Desc_d!"choose the new-lite one of shared free list",
		Implies_d!("slots", 8), Implies_d!("cache", 32));

	mixin DEF_OPT!("append", int, "-a <append-num>",
		Desc_d!"the number of nodes to append", Range_d!(0, 32), Default_d!2);

	mixin DEF_OPT!("slots", int, "-s <slots-num>",
		Desc_d!"the number of slots in new-lite mode", Range_d!(1, 64), Needs_d!"newLite");
	mixin DEF_OPT!("cache", int, "-x <cache-num>",
		Desc_d!"the limit of cache in new-lite mode", Range_d!(1, 256), Needs_d!"newLite");

	mixin DEF_OPT!("circle", int, "-c <num>", Range_d!(1, 100_000),
		Desc_d!"the circle times in each thread", Default_d!100);

	mixin DEF_OPT!("thnum", int, "-j <thnum>", Range_d!(1, 64),
		Desc_d!"the number of threads to excute", Default_d!4);

	mixin NEED_ONEOF_OPTS!(lite, nonLite, newLite);
	mixin END;

	void action()
	{
		bool is_lite = lite.get;
		bool is_no_lite = nonLite.get;
		bool is_new_lite = newLite.get;

		size_t circle_ = cast(size_t) circle.get;
		size_t thnum_ = cast(size_t) thnum.get;
		uint append_ = cast(uint) append.get;

		size_t slots_;
		uint cache_;
		if (is_new_lite)
		{
			slots_ = cast(size_t) slots.get;
			cache_ = cast(uint) cache.get;
		}

		string type_info = is_lite ? "lite" : is_no_lite ? "no-lite" : "new-lite";
		StopWatch sw;
		writefln("test type: %10s, circle: %s, thnum: %s, append: %s", type_info, circle_, thnum_, append_);
		if (is_new_lite)
			writefln("\tin new lite mode, slots: %s, cache-limit: %s", slots_, cache_);
		if (is_no_lite)
		{
			SharedAlloc salloc = SharedAlloc(64);
			salloc.appendNum = append_;
			salloc.baseAffinity = 4;
			test(&salloc, &sw, circle_, thnum_);
		}
		else if (is_lite)
		{
			SharedAllocLite salloc = SharedAllocLite(64);
			salloc.appendNum = append_;
			test(&salloc, &sw, circle_, thnum_);
		}
		else if (is_new_lite)
		{
			NSharedAlocLite nsalloc = NSharedAlocLite(64);
			nsalloc.initAllocatedSlots(slots_);
			nsalloc.appendNum = append_;
			nsalloc.cacheLimit = cache_;
			test(&nsalloc, &sw, circle_, thnum_, slots_);
		}
	}
}

mixin CMDLINE_MAIN!App;

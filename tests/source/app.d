import free_list;
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

alias Alloc = FreeList!(Mallocator, chooseAtRuntime, chooseAtRuntime, 32);
alias SharedAlloc = SharedFreelist!(Mallocator, 128, 1024, 32);

alias AllocLite = FreeListLite!(Mallocator, chooseAtRuntime, chooseAtRuntime, 32);
alias SharedAllocLite = SharedFreeListLite!(Mallocator, 128, 1024, 32);

alias NSharedAlocLite = NSharedFreelistLite!(Mallocator, 128, 1024, 64);

void test_alloc(Allocator)(Allocator* ptr_alloc, size_t circle)
{
	enum size_t bottom = 256;
	enum size_t top = 1025;
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

void test(Allocator)(Allocator* ptr_alloc, StopWatch* sw, size_t circle, size_t thnum)
{
	sw.start();
	foreach (_; 0 .. thnum)
	{
		spawn(&test_alloc!Allocator, ptr_alloc, circle);
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
	mixin DEF_BOOL_OPT!("newLite", "-m", Desc_d!"choose the new-lite one of shared free list");

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

		string type_info = is_lite ? "lite" : is_no_lite ? "no-lite" : "new-lite";
		StopWatch sw;
		writefln("test type: %10s, circle: %s, thnum: %s", type_info, circle_, thnum_);
		if (is_no_lite)
		{
			SharedAlloc salloc = SharedAlloc(64);
			salloc.appendNum = 4;
			salloc.baseAffinity = 4;
			test(&salloc, &sw, circle_, thnum_);
		}
		else if (is_lite)
		{
			SharedAllocLite salloc = SharedAllocLite(64);
			salloc.appendNum = 4;
			test(&salloc, &sw, circle_, thnum_);
		}
		else if (is_new_lite)
		{
			NSharedAlocLite nsalloc = NSharedAlocLite(64);
			nsalloc.appendNum = 4;
			test(&nsalloc, &sw, circle_, thnum_);
		}
	}
}

mixin CMDLINE_MAIN!App;

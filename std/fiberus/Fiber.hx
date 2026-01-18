/*
 * Fiberus Fiber - Fiber/coroutine API
 */
package fiberus;

/**
 * Represents a fiber (lightweight thread/coroutine).
 * Fibers are cooperatively scheduled - they must explicitly yield
 * to allow other fibers to run.
 */
@:native("Fiber")
extern class Fiber {
	/**
	 * Spawns a new fiber that will execute the given function.
	 * The fiber starts in the ready state and will be scheduled
	 * to run when the current fiber yields or completes.
	 *
	 * @param fn The function to execute in the new fiber (receives fiber arg)
	 * @return The newly created fiber
	 */
	public static function spawn(fn:Dynamic->Void):Fiber;

	/**
	 * Spawns a new fiber with a custom stack size.
	 *
	 * @param stackSize Stack size in bytes
	 * @param fn The function to execute (receives fiber arg)
	 * @return The newly created fiber
	 */
	public static function spawnWithStack(stackSize:Int, fn:Dynamic->Void):Fiber;

	/**
	 * Yields control from the current fiber, allowing other
	 * fibers to run. The current fiber will be rescheduled
	 * and continue from this point later.
	 */
	public static function yield():Void;

	/**
	 * Returns the currently executing fiber, or null if called
	 * from the main thread outside of any fiber.
	 */
	public static function current():Null<Fiber>;

	/**
	 * Returns whether the given fiber is still alive (not dead).
	 */
	public function isAlive():Bool;

	/**
	 * User data associated with this fiber.
	 */
	public var userData:Dynamic;

	// =========================================================================
	// Multithreading API
	// =========================================================================

	/**
	 * Creates worker threads for parallel fiber execution.
	 * This must be called before spawning fibers that should run in parallel.
	 * In single-threaded mode (default), this is a no-op that returns 0.
	 *
	 * @param count Number of worker threads to create
	 * @return Number of workers actually created (may be less than requested)
	 */
	public static function createWorkers(count:Int):Int;

	/**
	 * Returns the total number of threads (main + workers).
	 * In single-threaded mode, returns 1.
	 */
	public static function getThreadCount():Int;

	/**
	 * Returns the number of worker threads (excludes main thread).
	 * In single-threaded mode, returns 0.
	 */
	public static function getWorkerCount():Int;

	/**
	 * Spawns a fiber on a specific thread.
	 * If the thread ID is invalid, spawns on the current thread.
	 *
	 * @param threadId Target thread ID (0 = main thread)
	 * @param fn The function to execute
	 * @return The newly created fiber
	 */
	public static function spawnOn(threadId:Int, fn:Dynamic->Void):Fiber;

	/**
	 * Spawns a fiber on the least-loaded thread.
	 * Provides automatic load balancing across worker threads.
	 *
	 * @param fn The function to execute
	 * @return The newly created fiber
	 */
	public static function spawnAny(fn:Dynamic->Void):Fiber;
}

/**
 * Fiber state enumeration.
 */
enum FiberState {
	Ready;
	Running;
	Waiting;
	Dead;
}

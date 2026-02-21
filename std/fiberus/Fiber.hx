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
	 * 
	 * The fiber is pushed to the target thread's inbox and will be drained
	 * to its local work queue on the next scheduler iteration. This guarantees
	 * initial execution on the target thread, but the fiber may be stolen later.
	 * 
	 * If the thread ID is invalid or equals the current thread, falls back
	 * to local spawn for efficiency.
	 *
	 * @param threadId Target thread ID (0 = main thread, 1+ = workers)
	 * @param fn The function to execute
	 * @return The newly created fiber
	 */
	public static function spawnOn(threadId:Int, fn:Dynamic->Void):Fiber;

	/**
	 * Spawns a fiber on the least-loaded thread.
	 * 
	 * Uses Power of Two Choices algorithm: picks two random threads and
	 * spawns on the one with the smaller queue. This achieves near-optimal
	 * load distribution with O(1) overhead regardless of thread count.
	 * 
	 * In single-threaded mode, behaves identically to spawn().
	 *
	 * @param fn The function to execute
	 * @return The newly created fiber
	 */
	public static function spawnAny(fn:Dynamic->Void):Fiber;

	/**
	 * Returns the ID of the thread currently executing this code.
	 * 
	 * Thread IDs are:
	 * - 0 = main thread
	 * - 1+ = worker threads
	 * - -1 = scheduler not initialized
	 *
	 * Useful for debugging load distribution and implementing thread-local caches.
	 *
	 * @return Current thread ID
	 */
	public static function getThreadId():Int;

	/**
	 * Spawns multiple fibers with automatic round-robin distribution across threads.
	 * 
	 * More efficient than calling spawnAny in a loop for large batches because:
	 * - Single load-balance decision window (avoids stale samples)
	 * - Reduced per-fiber overhead
	 * - Better cache locality during creation
	 * 
	 * Each fiber's body receives its index (0 to count-1) as the first argument
	 * and the shared args value as the second argument.
	 *
	 * @param count Number of fibers to spawn
	 * @param body Function to execute in each fiber (receives index and args)
	 * @param args Shared argument passed to every fiber
	 * @return Number of fibers actually spawned (may be less on OOM)
	 */
	public static function spawnMany(count:Int, body:(index:Int, args:Dynamic) -> Void, args:Dynamic):Int;
}
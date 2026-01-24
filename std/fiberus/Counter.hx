/*
 * Fiberus Counter - Fiber synchronization primitive
 */
package fiberus;

/**
 * A Counter is used to synchronize fibers. Fibers can wait for a counter
 * to reach a target value (typically 0).
 *
 * Counters are GC-managed, so they will be automatically cleaned up when
 * no longer reachable. This makes them safe to capture in closures and
 * pass as function parameters.
 *
 * Usage pattern:
 * 1. Create counter with initial value = number of tasks
 * 2. Spawn fibers that call counter.decrement() when done
 * 3. Wait for counter to reach 0 with waitAndDone()
 *
 * Example:
 * ```haxe
 * var counter = Counter.create(3);  // 3 tasks
 * for (i in 0...3) {
 *     Fiber.spawn(function(_) {
 *         doWork(i);
 *         counter.decrement();
 *     });
 * }
 * counter.waitAndDone();  // Wait for all 3 and mark done
 * ```
 */
@:native("Counter")
extern class Counter {
	/**
	 * Creates a new counter with the given initial value.
	 * @param initialValue Starting count (typically number of tasks)
	 */
	public static function create(initialValue:Int):Counter;

	/**
	 * Adds delta to the counter value. Can be negative.
	 * @param delta Amount to add (can be negative)
	 */
	public function add(delta:Int):Void;

	/**
	 * Decrements the counter by 1. If this causes the counter
	 * to reach its target, all waiting fibers are woken.
	 * @return New value after decrement
	 */
	public function decrement():Int;

	/**
	 * Waits for the counter to reach the target value.
	 * If already at target, returns immediately.
	 * Otherwise, the current fiber is suspended until the target is reached.
	 * @param target Target value to wait for (default 0)
	 */
	public function wait(target:Int = 0):Void;

	/**
	 * Marks this counter as done (no longer in use).
	 *
	 * This is optional since counters are GC-managed, but calling done()
	 * is good practice as it:
	 * - Documents intent (counter lifecycle is complete)
	 * - Provides early warning if waiters still exist (debugging aid)
	 *
	 * WARNING: Do NOT call done() if fibers may still decrement this counter.
	 */
	public function done():Void;

	/**
	 * Waits for counter to reach target (default 0), then marks counter as done.
	 * This is the recommended pattern for most use cases.
	 *
	 * Equivalent to:
	 * ```haxe
	 * counter.wait(target);
	 * counter.done();
	 * ```
	 * @param target Target value to wait for (default 0)
	 */
	public function waitAndDone(target:Int = 0):Void;

	/**
	 * Returns the current value of the counter.
	 * Note: In multithreaded scenarios, the value may be stale by the time
	 * you use it. Use for debugging/logging only.
	 */
	public function getValue():Int;
}

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

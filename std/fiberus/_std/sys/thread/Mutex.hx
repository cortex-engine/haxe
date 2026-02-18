/*
 * Fiberus - Fiber Runtime for Haxe
 * Mutex.hx - No-op implementation for cooperative fiber scheduling.
 * Since fibers don't preempt each other, mutual exclusion is implicit.
 */

package sys.thread;

@:coreApi
class Mutex {
	public function new():Void {}

	public function acquire():Void {}

	public function tryAcquire():Bool {
		return true;
	}

	public function release():Void {}
}

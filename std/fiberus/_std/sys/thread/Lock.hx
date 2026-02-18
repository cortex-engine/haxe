/*
 * Fiberus - Fiber Runtime for Haxe
 * Lock.hx - Simple lock for cooperative fiber scheduling.
 * In cooperative mode, wait() returns immediately if already released,
 * otherwise it would need to yield the fiber (not yet implemented).
 */

package sys.thread;

@:coreApi
class Lock {
	var count:Int;

	public function new():Void {
		count = 0;
	}

	public function wait(?timeout:Float):Bool {
		if (count > 0) {
			count--;
			return true;
		}
		/* In cooperative scheduling without fiber yield support,
		   a lock wait with no release would deadlock. Return false on timeout. */
		return false;
	}

	public function release():Void {
		count++;
	}
}

/*
 * Fiberus - Fiber Runtime for Haxe
 * Lock.hx - Not supported on Fiberus target.
 */

package sys.thread;

@:coreApi
class Lock {
	public function new():Void {
		throw "sys.thread.Lock is not supported on Fiberus target";
	}

	public function wait(?timeout:Float):Bool {
		throw "sys.thread.Lock is not supported on Fiberus target";
	}

	public function release():Void {
		throw "sys.thread.Lock is not supported on Fiberus target";
	}
}

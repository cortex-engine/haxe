/*
 * Fiberus - Fiber Runtime for Haxe
 * Mutex.hx - Not supported on Fiberus target.
 */

package sys.thread;

@:coreApi
class Mutex {
	public function new():Void {
		throw "sys.thread.Mutex is not supported on Fiberus target";
	}

	public function acquire():Void {
		throw "sys.thread.Mutex is not supported on Fiberus target";
	}

	public function tryAcquire():Bool {
		throw "sys.thread.Mutex is not supported on Fiberus target";
	}

	public function release():Void {
		throw "sys.thread.Mutex is not supported on Fiberus target";
	}
}

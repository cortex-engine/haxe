/*
 * Fiberus - Fiber Runtime for Haxe
 * Semaphore.hx - Not supported on Fiberus target.
 */

package sys.thread;

@:coreApi
class Semaphore {
	public function new(value:Int):Void {
		throw "sys.thread.Semaphore is not supported on Fiberus target";
	}

	public function acquire():Void {
		throw "sys.thread.Semaphore is not supported on Fiberus target";
	}

	public function tryAcquire(?timeout:Float):Bool {
		throw "sys.thread.Semaphore is not supported on Fiberus target";
	}

	public function release():Void {
		throw "sys.thread.Semaphore is not supported on Fiberus target";
	}
}

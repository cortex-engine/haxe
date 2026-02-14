/*
 * Fiberus - Fiber Runtime for Haxe
 * Condition.hx - Not supported on Fiberus target.
 */

package sys.thread;

@:coreApi
class Condition {
	public function new():Void {
		throw "sys.thread.Condition is not supported on Fiberus target";
	}

	public function acquire():Void {
		throw "sys.thread.Condition is not supported on Fiberus target";
	}

	public function tryAcquire():Bool {
		throw "sys.thread.Condition is not supported on Fiberus target";
	}

	public function release():Void {
		throw "sys.thread.Condition is not supported on Fiberus target";
	}

	public function wait():Void {
		throw "sys.thread.Condition is not supported on Fiberus target";
	}

	public function signal():Void {
		throw "sys.thread.Condition is not supported on Fiberus target";
	}

	public function broadcast():Void {
		throw "sys.thread.Condition is not supported on Fiberus target";
	}
}

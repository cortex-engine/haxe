/*
 * Fiberus - Fiber Runtime for Haxe
 * Deque.hx - Not supported on Fiberus target.
 */

package sys.thread;

@:coreApi
class Deque<T> {
	public function new():Void {
		throw "sys.thread.Deque is not supported on Fiberus target";
	}

	public function add(i:T):Void {
		throw "sys.thread.Deque is not supported on Fiberus target";
	}

	public function push(i:T):Void {
		throw "sys.thread.Deque is not supported on Fiberus target";
	}

	public function pop(block:Bool):Null<T> {
		throw "sys.thread.Deque is not supported on Fiberus target";
	}
}

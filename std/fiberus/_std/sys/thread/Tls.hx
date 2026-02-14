/*
 * Fiberus - Fiber Runtime for Haxe
 * Tls.hx - Per-OS-thread local storage using slot-based scheme
 *
 * Each Tls instance gets a unique slot ID. Values are stored per-thread
 * using __thread (C11 _Thread_local) indexed by slot ID.
 */

package sys.thread;

@:coreApi
class Tls<T> {
	var slotId:Int;

	public var value(get, set):T;

	public function new():Void {
		slotId = untyped __fiberus__("fib_tls_alloc()");
	}

	function get_value():T {
		return untyped __fiberus__("fib_tls_get(", slotId, ")");
	}

	function set_value(v:T):T {
		untyped __fiberus__("fib_tls_set(", slotId, ", ", v, ")");
		return v;
	}
}

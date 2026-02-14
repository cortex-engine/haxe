/*
 * Fiberus - Fiber Runtime for Haxe
 * ThreadImpl.hx - Minimal stub. Only current() works, create() throws.
 */

package sys.thread;

abstract ThreadImpl(Int) {
	public static function create(f:Void->Void):ThreadImpl {
		throw "sys.thread.Thread.create is not supported on Fiberus target. Use fiberus.Fiber.spawn instead.";
	}

	public static function current():ThreadImpl {
		return cast 0;
	}

	public static function getName(t:ThreadImpl):Null<String> {
		return null;
	}

	public static function setName(t:ThreadImpl, name:String) {}
}

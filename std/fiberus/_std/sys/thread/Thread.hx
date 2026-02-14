/*
 * Fiberus - Fiber Runtime for Haxe
 * Thread.hx - Minimal Thread override for Fiberus
 *
 * Fiberus uses cooperative fibers, not OS threads.
 * Thread.create is not supported. Thread.current returns an opaque handle.
 * Only Tls is fully implemented (needed by many Haxe std lib internals).
 */

package sys.thread;

class Thread {

	static var mainThread:Thread;
	static var currentTLS:Tls<Thread>;

	var impl:ThreadImpl;

	public var events(default, null):Null<haxe.EventLoop>;
	public var isBlocking:Bool = true;
	public var name(default, set):Null<String>;
	public var isNative(default, null):Bool;

	function new(impl) {
		this.impl = impl;
	}

	function set_name(n) {
		name = n;
		return n;
	}

	public function toString() {
		return "Thread#" + (name ?? "fiberus");
	}

	public function sendMessage(msg:Dynamic) {
		throw "sys.thread.Thread.sendMessage is not supported on Fiberus target";
	}

	public function disposeNative() {}

	public static function readMessage(blocking:Bool):Null<Dynamic> {
		throw "sys.thread.Thread.readMessage is not supported on Fiberus target";
	}

	public static function current():Thread {
		var t = currentTLS.value;
		if (t != null)
			return t;
		var t = new Thread(ThreadImpl.current());
		t.isNative = true;
		currentTLS.value = t;
		return t;
	}

	public static inline function main() {
		return mainThread;
	}

	public static function create(?name:String, job:() -> Void, ?onAbort):Thread {
		throw "sys.thread.Thread.create is not supported on Fiberus target. Use fiberus.Fiber.spawn instead.";
	}

	public static function getAll() {
		return [current()];
	}

	public dynamic function onAbort(e:haxe.Exception) {
		Sys.println("THREAD ABORTED : " + e.message + haxe.CallStack.toString(e.stack));
	}

	static function hasBlocking() {
		return false;
	}

	static function __init__() {
		mainThread = new Thread(ThreadImpl.current());
		mainThread.name = "Main";
		mainThread.events = haxe.EventLoop.main;
		mainThread.events.thread = mainThread;
		currentTLS = new Tls();
		currentTLS.value = mainThread;
	}
}

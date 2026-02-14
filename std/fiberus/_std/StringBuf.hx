/*
 * Fiberus StringBuf - Efficient string building using a C-backed growable buffer.
 *
 * Unlike the default StringBuf (which uses b += x causing O(n^2) behavior),
 * this implementation uses a malloc'd byte buffer with O(1) amortized appends.
 * The buffer is converted to a GC-managed FibString on toString().
 */

@:coreApi
class StringBuf {
	var b:fiberus.FibStringBufPtr;

	public var length(get, never):Int;

	public function new():Void {
		b = untyped __fiberus__("fib_strbuf_new()");
	}

	function get_length():Int {
		return untyped __fiberus__("(int32_t)fib_strbuf_char_length(", b, ")");
	}

	public function add<T>(x:T):Void {
		var s:String = Std.string(x);
		untyped __fiberus__("fib_strbuf_add_string(", b, ", ", s, ")");
	}

	public function addChar(c:Int):Void {
		untyped __fiberus__("fib_strbuf_add_char(", b, ", ", c, ")");
	}

	public function addSub(s:String, pos:Int, ?len:Int):Void {
		/* Use substr to handle codepoint-based indices, then append the result */
		var sub:String;
		if (len == null) {
			sub = s.substr(pos);
		} else {
			/* Extract int from Null<Int> to avoid FibDynamic→size_t codegen issue */
			var l:Int = len;
			sub = s.substr(pos, l);
		}
		untyped __fiberus__("fib_strbuf_add_string(", b, ", ", sub, ")");
	}

	public function clear():Void {
		untyped __fiberus__("fib_strbuf_clear(", b, ")");
	}

	public function toString():String {
		return untyped __fiberus__("fib_strbuf_to_string(", b, ")");
	}
}

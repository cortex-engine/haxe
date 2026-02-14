/*
 * Fiberus haxe.Utf8 - UTF-8 string operations backed by simdutf.
 *
 * Since Fiberus strings are natively UTF-8 with codepoint-based indexing,
 * most methods delegate directly to String. The key additions are:
 * - encode/decode for Latin-1 <-> UTF-8 conversion (SIMD-accelerated via simdutf)
 * - validate for actual UTF-8 validation (SIMD-accelerated via simdutf)
 * - addChar using the efficient fib_strbuf_add_char C function
 */

package haxe;

@:coreApi
@:deprecated('haxe.Utf8 is deprecated. Use UnicodeString instead.')
class Utf8 {
	var __b:fiberus.FibStringBufPtr;

	public function new(?size:Int):Void {
		__b = untyped __fiberus__("fib_strbuf_new()");
	}

	public function addChar(c:Int):Void {
		untyped __fiberus__("fib_strbuf_add_char(", __b, ", ", c, ")");
	}

	public function toString():String {
		return untyped __fiberus__("fib_strbuf_to_string(", __b, ")");
	}

	public static function encode(s:String):String {
		return untyped __fiberus__("fib_utf8_encode_latin1(", s, ")");
	}

	public static function decode(s:String):String {
		return untyped __fiberus__("fib_utf8_decode_to_latin1(", s, ")");
	}

	public static function iter(s:String, chars:Int->Void):Void {
		for (i in 0...s.length)
			chars(s.charCodeAt(i));
	}

	public static inline function charCodeAt(s:String, index:Int):Int {
		return s.charCodeAt(index);
	}

	public static function validate(s:String):Bool {
		return untyped __fiberus__("simdutf_validate_utf8(fib_string_data(", s, "), fib_string_byte_length(", s, "))");
	}

	public static inline function length(s:String):Int {
		return s.length;
	}

	public static function compare(a:String, b:String):Int {
		return untyped __fiberus__("fib_string_compare(", a, ", ", b, ")");
	}

	public static inline function sub(s:String, pos:Int, len:Int):String {
		return s.substr(pos, len);
	}
}

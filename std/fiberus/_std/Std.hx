/*
 * Fiberus Std - Standard library implementation
 */

@:coreApi
class Std {
	@:deprecated('Std.is is deprecated. Use Std.isOfType instead.')
	public static inline function is(v:Dynamic, t:Dynamic):Bool {
		return isOfType(v, t);
	}

	public static function isOfType(v:Dynamic, t:Dynamic):Bool {
		return untyped fiberus.Boot.__instanceof(v, t);
	}

	public static inline function downcast<T:{}, S:T>(value:T, c:Class<S>):Null<S> {
		return isOfType(value, c) ? cast value : null;
	}

	@:deprecated('Std.instance() is deprecated. Use Std.downcast() instead.')
	public static inline function instance<T:{}, S:T>(value:T, c:Class<S>):Null<S> {
		return downcast(value, c);
	}

	public static function string(s:Dynamic):String {
		if (s == null)
			return "null";
		if (Std.isOfType(s, String))
			return s;
		return untyped fiberus.Boot.__string_rec(s, "");
	}

	public static function int(x:Float):Int {
		if (x != x) // NaN check
			return 0;
		return untyped __fiberus__("(int32_t)", x);
	}

	public static function parseInt(x:String):Null<Int> {
		if (x == null)
			return null;
		return untyped __fiberus__("fib_string_parse_int(", x, ")");
	}

	public static function parseFloat(x:String):Float {
		if (x == null)
			return Math.NaN;
		return untyped __fiberus__("fib_string_parse_float(", x, ")");
	}

	public static function random(x:Int):Int {
		if (x <= 0)
			return 0;
		return untyped __fiberus__("rand() %", x);
	}
}

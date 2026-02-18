/*
 * Fiberus - Fiber Runtime for Haxe
 * FPHelper.hx - Floating point helper for fiberus target
 *
 * Uses memcpy-based bit reinterpretation for exact IEEE 754 conversion,
 * matching hxcpp's pointer-cast approach.
 */

package haxe.io;

class FPHelper {
	public static inline function i32ToFloat(i:Int):Float {
		return untyped __fiberus__("fib_i32_to_float(", i, ")");
	}

	public static inline function floatToI32(f:Float):Int {
		return untyped __fiberus__("fib_float_to_i32(", f, ")");
	}

	public static inline function i64ToDouble(low:Int, high:Int):Float {
		return untyped __fiberus__("fib_i64_to_double(", low, ", ", high, ")");
	}

	public static inline function doubleToI64(v:Float):Int64 {
		return untyped __fiberus__("fib_double_to_i64(", v, ")");
	}
}

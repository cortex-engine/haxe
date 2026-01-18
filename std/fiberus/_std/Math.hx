/*
 * Fiberus Math - Math functions implementation using C standard library
 */

@:coreApi
class Math {
	public static var PI(default, null):Float = 3.141592653589793;
	public static var NEGATIVE_INFINITY(default, null):Float = untyped __fiberus__("-INFINITY");
	public static var POSITIVE_INFINITY(default, null):Float = untyped __fiberus__("INFINITY");
	public static var NaN(default, null):Float = untyped __fiberus__("NAN");

	public static inline function abs(v:Float):Float {
		return untyped __fiberus__("fabs(", v, ")");
	}

	public static inline function min(a:Float, b:Float):Float {
		return untyped __fiberus__("fmin(", a, ", ", b, ")");
	}

	public static inline function max(a:Float, b:Float):Float {
		return untyped __fiberus__("fmax(", a, ", ", b, ")");
	}

	public static inline function sin(v:Float):Float {
		return untyped __fiberus__("sin(", v, ")");
	}

	public static inline function cos(v:Float):Float {
		return untyped __fiberus__("cos(", v, ")");
	}

	public static inline function tan(v:Float):Float {
		return untyped __fiberus__("tan(", v, ")");
	}

	public static inline function asin(v:Float):Float {
		return untyped __fiberus__("asin(", v, ")");
	}

	public static inline function acos(v:Float):Float {
		return untyped __fiberus__("acos(", v, ")");
	}

	public static inline function atan(v:Float):Float {
		return untyped __fiberus__("atan(", v, ")");
	}

	public static inline function atan2(y:Float, x:Float):Float {
		return untyped __fiberus__("atan2(", y, ", ", x, ")");
	}

	public static inline function exp(v:Float):Float {
		return untyped __fiberus__("exp(", v, ")");
	}

	public static inline function log(v:Float):Float {
		return untyped __fiberus__("log(", v, ")");
	}

	public static inline function pow(v:Float, exp:Float):Float {
		return untyped __fiberus__("pow(", v, ", ", exp, ")");
	}

	public static inline function sqrt(v:Float):Float {
		return untyped __fiberus__("sqrt(", v, ")");
	}

	public static inline function round(v:Float):Int {
		return untyped __fiberus__("(int32_t)round(", v, ")");
	}

	public static inline function floor(v:Float):Int {
		return untyped __fiberus__("(int32_t)floor(", v, ")");
	}

	public static inline function ceil(v:Float):Int {
		return untyped __fiberus__("(int32_t)ceil(", v, ")");
	}

	public static inline function ffloor(v:Float):Float {
		return untyped __fiberus__("floor(", v, ")");
	}

	public static inline function fceil(v:Float):Float {
		return untyped __fiberus__("ceil(", v, ")");
	}

	public static inline function fround(v:Float):Float {
		return untyped __fiberus__("round(", v, ")");
	}

	public static inline function random():Float {
		return untyped __fiberus__("((double)rand() / (double)RAND_MAX)");
	}

	public static inline function isFinite(f:Float):Bool {
		return untyped __fiberus__("isfinite(", f, ")");
	}

	public static inline function isNaN(f:Float):Bool {
		return untyped __fiberus__("isnan(", f, ")");
	}
}

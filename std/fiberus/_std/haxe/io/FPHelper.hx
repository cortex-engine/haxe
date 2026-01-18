/*
 * Fiberus - Fiber Runtime for Haxe
 * FPHelper.hx - Floating point helper for fiberus target
 *
 * Uses native 64-bit integers, so we use Int64.make() instead of set_low/set_high.
 */

package haxe.io;

class FPHelper {
	static inline var LN2 = 0.6931471805599453; // Math.log(2)

	static inline function _i32ToFloat(i:Int):Float {
		var sign = 1 - ((i >>> 31) << 1);
		var e = (i >> 23) & 0xff;
		if (e == 255)
			return i & 0x7fffff == 0 ? (sign > 0 ? Math.POSITIVE_INFINITY : Math.NEGATIVE_INFINITY) : Math.NaN;
		var m = e == 0 ? (i & 0x7fffff) << 1 : (i & 0x7fffff) | 0x800000;
		return sign * m * Math.pow(2, e - 150);
	}

	static inline function _i64ToDouble(lo:Int, hi:Int):Float {
		var sign = 1 - ((hi >>> 31) << 1);
		var e = (hi >> 20) & 0x7ff;
		if (e == 2047)
			return lo == 0 && (hi & 0xFFFFF) == 0 ? (sign > 0 ? Math.POSITIVE_INFINITY : Math.NEGATIVE_INFINITY) : Math.NaN;
		var m = 2.220446049250313e-16 * ((hi & 0xFFFFF) * 4294967296. + (lo >>> 31) * 2147483648. + (lo & 0x7FFFFFFF));
		m = e == 0 ? m * 2.0 : m + 1.0;
		return sign * m * Math.pow(2, e - 1023);
	}

	static inline function _floatToI32(f:Float):Int {
		if (f == 0)
			return 0;
		var af = f < 0 ? -f : f;
		var exp = Math.floor(Math.log(af) / LN2);
		if (exp > 127) {
			return 0x7F800000;
		} else {
			if (exp <= -127) {
				exp = -127;
				af *= 7.1362384635298e+44; // af * 0.5 * 0x800000 / Math.pow(2, -127)
			} else {
				af = (af / Math.pow(2, exp) - 1.0) * 0x800000;
			}
			return (f < 0 ? 0x80000000 : 0) | ((exp + 127) << 23) | Math.round(af);
		}
	}

	static inline function _doubleToI64(v:Float):Int64 {
		if (v == 0) {
			return Int64.make(0, 0);
		} else if (!Math.isFinite(v)) {
			return Int64.make(v > 0 ? 0x7FF00000 : 0xFFF00000, 0);
		} else {
			var av = v < 0 ? -v : v;
			var exp = Math.floor(Math.log(av) / LN2);
			if (exp > 1023) {
				return Int64.make(0x7FEFFFFF, 0xFFFFFFFF);
			} else {
				if (exp <= -1023) {
					exp = -1023;
					av = av / 2.2250738585072014e-308;
				} else {
					av = av / Math.pow(2, exp) - 1.0;
				}
				var sig = Math.fround(av * 4503599627370496.); // 2^52
				var sig_l = Std.int(sig);
				var sig_h = Std.int(sig / 4294967296.0);
				return Int64.make((v < 0 ? 0x80000000 : 0) | ((exp + 1023) << 20) | sig_h, sig_l);
			}
		}
	}

	public static function i32ToFloat(i:Int):Float {
		return _i32ToFloat(i);
	}

	public static function floatToI32(f:Float):Int {
		return _floatToI32(f);
	}

	public static function i64ToDouble(low:Int, high:Int):Float {
		return _i64ToDouble(low, high);
	}

	/**
		Returns an Int64 representing the bytes representation of the double precision IEEE float value.
	**/
	public static function doubleToI64(v:Float):Int64 {
		return _doubleToI64(v);
	}
}

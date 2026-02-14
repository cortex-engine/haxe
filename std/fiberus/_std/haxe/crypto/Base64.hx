/*
 * Fiberus override for haxe.crypto.Base64
 * Uses SIMD-accelerated base64 via simdutf for high-performance encode/decode.
 */

package haxe.crypto;

class Base64 {
	public static var CHARS(default, null) = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
	public static var BYTES(default, null) = haxe.io.Bytes.ofString(CHARS);

	public static var URL_CHARS(default, null) = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
	public static var URL_BYTES(default, null) = haxe.io.Bytes.ofString(URL_CHARS);

	public static function encode(bytes:haxe.io.Bytes, complement = true):String {
		return untyped __fiberus__("fib_base64_encode(", bytes, "->b, ", complement, ")");
	}

	public static function decode(str:String, complement = true):haxe.io.Bytes {
		/* complement parameter ignored - simdutf handles padding automatically */
		var bd:haxe.io.BytesData = untyped __fiberus__("fib_base64_decode(", str, ")");
		return haxe.io.Bytes.ofData(bd);
	}

	public static function urlEncode(bytes:haxe.io.Bytes, complement = false):String {
		return untyped __fiberus__("fib_base64url_encode(", bytes, "->b, ", complement, ")");
	}

	public static function urlDecode(str:String, complement = false):haxe.io.Bytes {
		var bd:haxe.io.BytesData = untyped __fiberus__("fib_base64url_decode(", str, ")");
		return haxe.io.Bytes.ofData(bd);
	}
}

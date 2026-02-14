package sys.ssl;

import haxe.io.Bytes;
import haxe.io.BytesData;

@:coreApi
class Digest {
	public static function make(data:haxe.io.Bytes, alg:DigestAlgorithm):haxe.io.Bytes {
		var algStr:String = cast alg;
		var bd:BytesData = untyped __fiberus__("(FibBytesData*)fib_ssl_dgst_make(fib_bytes_data(", data, "->b), fib_bytes_length(", data,
			"->b), fib_string_data(", algStr, "))");
		var isNull:Bool = untyped __fiberus__("(", bd, " == NULL)");
		if (isNull)
			throw "Invalid hash algorithm";
		return Bytes.ofData(bd);
	}

	public static function sign(data:haxe.io.Bytes, privKey:Key, alg:DigestAlgorithm):haxe.io.Bytes {
		var algStr:String = cast alg;
		var keyPtr:haxe.Int64 = @:privateAccess privKey.__k;
		var bd:BytesData = untyped __fiberus__("(FibBytesData*)fib_ssl_dgst_sign(fib_bytes_data(", data, "->b), fib_bytes_length(", data,
			"->b), (FibSSLKey*)", keyPtr, ", fib_string_data(", algStr, "))");
		var isNull:Bool = untyped __fiberus__("(", bd, " == NULL)");
		if (isNull)
			throw "Digest sign failed";
		return Bytes.ofData(bd);
	}

	public static function verify(data:haxe.io.Bytes, signature:haxe.io.Bytes, pubKey:Key, alg:DigestAlgorithm):Bool {
		var algStr:String = cast alg;
		var keyPtr:haxe.Int64 = @:privateAccess pubKey.__k;
		var r:Int = untyped __fiberus__("fib_ssl_dgst_verify(fib_bytes_data(", data, "->b), fib_bytes_length(", data,
			"->b), fib_bytes_data(", signature, "->b), fib_bytes_length(", signature, "->b), (FibSSLKey*)", keyPtr,
			", fib_string_data(", algStr, "))");
		return r == 0;
	}
}

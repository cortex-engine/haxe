package sys.ssl;

@:coreApi
class Key {
	var __k:haxe.Int64; /* FibSSLKey* stored as intptr_t */

	function new(k:haxe.Int64) {
		__k = k;
	}

	public static function loadFile(file:String, ?isPublic:Bool, ?pass:String):Key {
		var data = sys.io.File.getBytes(file);
		var str = data.toString();
		if (str.indexOf("-----BEGIN ") >= 0)
			return readPEM(str, isPublic == true, pass);
		else
			return readDER(data, isPublic == true);
	}

	public static function readPEM(data:String, isPublic:Bool, ?pass:String):Key {
		var key:haxe.Int64 = untyped __fiberus__("(intptr_t)fib_ssl_key_new()");
		if (key == 0)
			throw "Failed to allocate key";

		var r:Int;
		if (pass != null) {
			r = untyped __fiberus__("fib_ssl_key_parse_pem((FibSSLKey*)", key,
				", (const unsigned char*)fib_string_data(", data, "), fib_string_length(", data,
				") + 1, (const unsigned char*)fib_string_data(", pass, "), fib_string_length(", pass, "), ", isPublic, ")");
		} else {
			r = untyped __fiberus__("fib_ssl_key_parse_pem((FibSSLKey*)", key,
				", (const unsigned char*)fib_string_data(", data, "), fib_string_length(", data,
				") + 1, NULL, 0, ", isPublic, ")");
		}
		if (r != 0) {
			untyped __fiberus__("fib_ssl_key_free((FibSSLKey*)", key, ")");
			throw "Failed to parse PEM key";
		}
		return new Key(key);
	}

	public static function readDER(data:haxe.io.Bytes, isPublic:Bool):Key {
		var key:haxe.Int64 = untyped __fiberus__("(intptr_t)fib_ssl_key_new()");
		if (key == 0)
			throw "Failed to allocate key";
		var r:Int = untyped __fiberus__("fib_ssl_key_parse_der((FibSSLKey*)", key,
			", fib_bytes_data(", data, "->b), fib_bytes_length(", data, "->b), ", isPublic, ")");
		if (r != 0) {
			untyped __fiberus__("fib_ssl_key_free((FibSSLKey*)", key, ")");
			throw "Failed to parse DER key";
		}
		return new Key(key);
	}

	static function __init__():Void {
		untyped __fiberus__("fib_ssl_init()");
	}
}

package sys.ssl;

@:coreApi
class Certificate {
	var __x:haxe.Int64; /* FibSSLCert* stored as intptr_t */
	var __h:Null<Certificate>; /* head reference to prevent GC of chain root */

	@:allow(sys.ssl.Socket)
	function new(x:haxe.Int64, ?h:Certificate) {
		__x = x;
		__h = h;
	}

	public static function loadFile(file:String):Certificate {
		var cert:haxe.Int64 = untyped __fiberus__("(intptr_t)fib_ssl_cert_new()");
		if (cert == 0)
			throw "Failed to allocate certificate";
		var r:Int = untyped __fiberus__("fib_ssl_cert_parse_file((FibSSLCert*)", cert, ", fib_string_data(", file, "))");
		if (r != 0) {
			untyped __fiberus__("fib_ssl_cert_free((FibSSLCert*)", cert, ")");
			throw "Failed to load certificate file";
		}
		return new Certificate(cert);
	}

	public static function loadPath(path:String):Certificate {
		var cert:haxe.Int64 = untyped __fiberus__("(intptr_t)fib_ssl_cert_new()");
		if (cert == 0)
			throw "Failed to allocate certificate";
		var r:Int = untyped __fiberus__("fib_ssl_cert_parse_path((FibSSLCert*)", cert, ", fib_string_data(", path, "))");
		if (r != 0) {
			untyped __fiberus__("fib_ssl_cert_free((FibSSLCert*)", cert, ")");
			throw "Failed to load certificate path";
		}
		return new Certificate(cert);
	}

	public static function fromString(str:String):Certificate {
		var cert:haxe.Int64 = untyped __fiberus__("(intptr_t)fib_ssl_cert_new()");
		if (cert == 0)
			throw "Failed to allocate certificate";
		/* mbedTLS requires PEM to be null-terminated, str is already null-terminated in FibString */
		var r:Int = untyped __fiberus__("fib_ssl_cert_parse_pem((FibSSLCert*)", cert,
			", (const unsigned char*)fib_string_data(", str, "), fib_string_length(", str, ") + 1)");
		if (r < 0) {
			untyped __fiberus__("fib_ssl_cert_free((FibSSLCert*)", cert, ")");
			throw "Failed to parse PEM certificate";
		}
		return new Certificate(cert);
	}

	public static function loadDefaults():Certificate {
		/* Linux: scan well-known filesystem paths for CA bundles */
		var defPaths = [
			"/etc/ssl/certs/ca-certificates.crt", // Debian/Ubuntu/Gentoo
			"/etc/pki/tls/certs/ca-bundle.crt", // Fedora/RHEL
			"/etc/ssl/ca-bundle.pem", // OpenSUSE
			"/etc/pki/tls/cacert.pem", // OpenELEC
			"/etc/ssl/certs", // SLES10/SLES11 (directory)
			"/system/etc/security/cacerts" // Android
		];
		for (path in defPaths) {
			if (sys.FileSystem.exists(path)) {
				if (sys.FileSystem.isDirectory(path))
					return loadPath(path);
				else
					return loadFile(path);
			}
		}
		return null;
	}

	public var commonName(get, null):Null<String>;
	public var altNames(get, null):Array<String>;
	public var notBefore(get, null):Date;
	public var notAfter(get, null):Date;

	function get_commonName():Null<String> {
		return subject("CN");
	}

	function get_altNames():Array<String> {
		/* Get alt names from C as FibArray* of FibDynamic (FIB_TYPE_STRING) */
		var arr:haxe.Int64 = untyped __fiberus__("(intptr_t)fib_ssl_cert_altnames((FibSSLCert*)", __x, ")");
		if (arr == 0)
			return [];
		var result:Array<String> = [];
		var len:Int = untyped __fiberus__("((FibArray*)", arr, ")->length");
		var i = 0;
		while (i < len) {
			var s:String = untyped __fiberus__("(FibString*)fib_array_get((FibArray*)", arr, ", ", i, ").data.ptrVal");
			result.push(s);
			i++;
		}
		return result;
	}

	public function subject(field:String):Null<String> {
		var s:String = untyped __fiberus__("(FibString*)fib_ssl_cert_subject((FibSSLCert*)", __x,
			", fib_string_data(", field, "))");
		return s;
	}

	public function issuer(field:String):Null<String> {
		var s:String = untyped __fiberus__("(FibString*)fib_ssl_cert_issuer((FibSSLCert*)", __x,
			", fib_string_data(", field, "))");
		return s;
	}

	function get_notBefore():Date {
		var year:Int = 0;
		var mon:Int = 0;
		var day:Int = 0;
		var hour:Int = 0;
		var min:Int = 0;
		var sec:Int = 0;
		untyped __fiberus__("{ int _t[6]; fib_ssl_cert_notbefore((FibSSLCert*)", __x, ", _t); ",
			year, " = _t[0]; ", mon, " = _t[1]; ", day, " = _t[2]; ",
			hour, " = _t[3]; ", min, " = _t[4]; ", sec, " = _t[5]; }");
		return new Date(year, mon - 1, day, hour, min, sec);
	}

	function get_notAfter():Date {
		var year:Int = 0;
		var mon:Int = 0;
		var day:Int = 0;
		var hour:Int = 0;
		var min:Int = 0;
		var sec:Int = 0;
		untyped __fiberus__("{ int _t[6]; fib_ssl_cert_notafter((FibSSLCert*)", __x, ", _t); ",
			year, " = _t[0]; ", mon, " = _t[1]; ", day, " = _t[2]; ",
			hour, " = _t[3]; ", min, " = _t[4]; ", sec, " = _t[5]; }");
		return new Date(year, mon - 1, day, hour, min, sec);
	}

	public function next():Null<Certificate> {
		var n:haxe.Int64 = untyped __fiberus__("(intptr_t)fib_ssl_cert_next((FibSSLCert*)", __x, ")");
		return n == 0 ? null : new Certificate(n, __h == null ? this : __h);
	}

	public function add(pem:String):Void {
		var r:Int = untyped __fiberus__("fib_ssl_cert_parse_pem((FibSSLCert*)", __x,
			", (const unsigned char*)fib_string_data(", pem, "), fib_string_length(", pem, ") + 1)");
		if (r < 0)
			throw "Failed to add PEM certificate";
	}

	public function addDER(der:haxe.io.Bytes):Void {
		var r:Int = untyped __fiberus__("fib_ssl_cert_parse_der((FibSSLCert*)", __x,
			", fib_bytes_data(", der, "->b), fib_bytes_length(", der, "->b))");
		if (r < 0)
			throw "Failed to add DER certificate";
	}

	static function __init__():Void {
		untyped __fiberus__("fib_ssl_init()");
	}
}

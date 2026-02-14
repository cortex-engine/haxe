package sys.ssl;

import fiberus.io.FD;
import fiberus.io.OpenFlags;

private class SSLInput extends haxe.io.Input {
	var socket:Socket;

	public function new(s:Socket) {
		this.socket = s;
	}

	override public function readByte():Int {
		socket.handshake();
		var buf = haxe.io.Bytes.alloc(1);
		var sslCtx:haxe.Int64 = @:privateAccess socket.sslCtx;
		var r:Int = untyped __fiberus__("fib_ssl_read((FibSSLContext*)", sslCtx, ", fib_bytes_data(", buf, "->b), 1)");
		if (r <= 0)
			throw new haxe.io.Eof();
		return buf.get(0);
	}

	override public function readBytes(s:haxe.io.Bytes, pos:Int, len:Int):Int {
		socket.handshake();
		var sslCtx:haxe.Int64 = @:privateAccess socket.sslCtx;
		var r:Int = untyped __fiberus__("fib_ssl_read((FibSSLContext*)", sslCtx,
			", fib_bytes_data(", s, "->b) + ", pos, ", ", len, ")");
		if (r == 0)
			throw new haxe.io.Eof();
		if (r < 0) {
			var errMsg:String = untyped __fiberus__("fib_string_new(fib_ssl_strerror(", r, "))");
			throw haxe.io.Error.Custom("SSL read error: " + errMsg);
		}
		return r;
	}

	override public function close():Void {
		super.close();
		if (socket != null)
			socket.close();
	}
}

private class SSLOutput extends haxe.io.Output {
	var socket:Socket;

	public function new(s:Socket) {
		this.socket = s;
	}

	override public function writeByte(c:Int):Void {
		socket.handshake();
		var buf = haxe.io.Bytes.alloc(1);
		buf.set(0, c);
		var sslCtx:haxe.Int64 = @:privateAccess socket.sslCtx;
		var r:Int = untyped __fiberus__("fib_ssl_write((FibSSLContext*)", sslCtx,
			", fib_bytes_data(", buf, "->b), 1)");
		if (r < 0) {
			var errMsg:String = untyped __fiberus__("fib_string_new(fib_ssl_strerror(", r, "))");
			throw haxe.io.Error.Custom("SSL write error: " + errMsg);
		}
	}

	override public function writeBytes(s:haxe.io.Bytes, pos:Int, len:Int):Int {
		socket.handshake();
		var sslCtx:haxe.Int64 = @:privateAccess socket.sslCtx;
		var r:Int = untyped __fiberus__("fib_ssl_write((FibSSLContext*)", sslCtx,
			", fib_bytes_data(", s, "->b) + ", pos, ", ", len, ")");
		if (r < 0) {
			var errMsg:String = untyped __fiberus__("fib_string_new(fib_ssl_strerror(", r, "))");
			throw haxe.io.Error.Custom("SSL write error: " + errMsg);
		}
		return r;
	}

	override public function close():Void {
		super.close();
		if (socket != null)
			socket.close();
	}
}

@:coreApi
class Socket extends sys.net.Socket {
	public static var DEFAULT_VERIFY_CERT:Null<Bool>;
	public static var DEFAULT_CA:Null<sys.ssl.Certificate>;

	public var verifyCert:Null<Bool>;

	var sslConf:haxe.Int64; /* FibSSLConfig* as intptr_t */
	var sslCtx:haxe.Int64; /* FibSSLContext* as intptr_t */
	var caCert:Null<sys.ssl.Certificate>;
	var hostname:String;
	var ownCert:Null<sys.ssl.Certificate>;
	var ownKey:Null<sys.ssl.Key>;
	var handshakeDone:Bool;

	public function new() {
		super();
		sslConf = haxe.Int64.ofInt(0);
		sslCtx = haxe.Int64.ofInt(0);
		handshakeDone = false;

		if (DEFAULT_VERIFY_CERT == true && DEFAULT_CA == null) {
			try {
				DEFAULT_CA = sys.ssl.Certificate.loadDefaults();
			} catch (e:Dynamic) {}
		}
		caCert = DEFAULT_CA;
		verifyCert = DEFAULT_VERIFY_CERT;
	}

	override public function connect(host:sys.net.Host, port:Int):Void {
		/* Build SSL config */
		sslConf = buildSSLConfig(false);
		if (sslConf == 0)
			throw "Failed to create SSL configuration";

		/* Create SSL context */
		sslCtx = untyped __fiberus__("(intptr_t)fib_ssl_new((FibSSLConfig*)", sslConf, ")");
		if (sslCtx == 0)
			throw "Failed to create SSL context";

		handshakeDone = false;

		/* Bind the socket fd to the SSL context */
		var socketFd = getFd();
		untyped __fiberus__("fib_ssl_set_fd((FibSSLContext*)", sslCtx, ", ", socketFd, ")");

		/* Set hostname for SNI */
		if (hostname == null)
			hostname = host.toString();
		if (hostname != null)
			untyped __fiberus__("fib_ssl_set_hostname((FibSSLContext*)", sslCtx, ", fib_string_data(", hostname, "))");

		/* TCP connect first (via parent class) */
		super.connect(host, port);

		/* Replace I/O streams with SSL versions */
		input = new SSLInput(this);
		output = new SSLOutput(this);

		/* Perform SSL handshake */
		handshake();
	}

	override public function read():String {
		handshake();
		var buf = new haxe.io.BytesBuffer();
		var chunk = haxe.io.Bytes.alloc(4096);
		while (true) {
			var n:Int = untyped __fiberus__("fib_ssl_read((FibSSLContext*)", sslCtx,
				", fib_bytes_data(", chunk, "->b), 4096)");
			if (n <= 0) break;
			buf.addBytes(chunk, 0, n);
		}
		return buf.getBytes().toString();
	}

	override public function write(content:String):Void {
		handshake();
		var bytes = haxe.io.Bytes.ofString(content);
		var pos = 0;
		while (pos < bytes.length) {
			var remaining = bytes.length - pos;
			var n:Int = untyped __fiberus__("fib_ssl_write((FibSSLContext*)", sslCtx,
				", fib_bytes_data(", bytes, "->b) + ", pos, ", ", remaining, ")");
			if (n < 0) {
				var errMsg:String = untyped __fiberus__("fib_string_new(fib_ssl_strerror(", n, "))");
				throw haxe.io.Error.Custom("SSL write error: " + errMsg);
			}
			pos += n;
		}
	}

	public function handshake():Void {
		if (!handshakeDone) {
			var r:Int = untyped __fiberus__("fib_ssl_handshake((FibSSLContext*)", sslCtx, ")");
			if (r != 0) {
				var errMsg:String = untyped __fiberus__("fib_string_new(fib_ssl_strerror(", r, "))");
				throw "SSL handshake failed: " + errMsg;
			}
			handshakeDone = true;
		}
	}

	public function setCA(cert:sys.ssl.Certificate):Void {
		caCert = cert;
	}

	public function setHostname(name:String):Void {
		hostname = name;
	}

	public function setCertificate(cert:Certificate, key:Key):Void {
		ownCert = cert;
		ownKey = key;
	}

	public function addSNICertificate(cbServernameMatch:String->Bool, cert:Certificate, key:Key):Void {
		/* SNI callback not yet implemented for Fiberus */
		throw new haxe.exceptions.NotImplementedException();
	}

	public function peerCertificate():sys.ssl.Certificate {
		var crt:haxe.Int64 = untyped __fiberus__("(intptr_t)fib_ssl_get_peer_cert((FibSSLContext*)", sslCtx, ")");
		if (crt == 0)
			return null;
		return @:privateAccess new sys.ssl.Certificate(crt);
	}

	override public function close():Void {
		if (sslCtx != 0) {
			untyped __fiberus__("fib_ssl_close((FibSSLContext*)", sslCtx, ")");
			sslCtx = haxe.Int64.ofInt(0);
		}
		if (sslConf != 0) {
			untyped __fiberus__("fib_ssl_conf_close((FibSSLConfig*)", sslConf, ")");
			sslConf = haxe.Int64.ofInt(0);
		}
		super.close();
	}

	function buildSSLConfig(server:Bool):haxe.Int64 {
		var conf:haxe.Int64 = untyped __fiberus__("(intptr_t)fib_ssl_conf_new(", server, ")");
		if (conf == 0)
			return haxe.Int64.ofInt(0);

		/* Set own certificate if provided */
		if (ownCert != null && ownKey != null) {
			var certPtr:haxe.Int64 = @:privateAccess ownCert.__x;
			var keyPtr:haxe.Int64 = @:privateAccess ownKey.__k;
			untyped __fiberus__("fib_ssl_conf_set_cert((FibSSLConfig*)", conf,
				", (FibSSLCert*)", certPtr, ", (FibSSLKey*)", keyPtr, ")");
		}

		/* Set CA chain */
		if (caCert != null) {
			var caPtr:haxe.Int64 = @:privateAccess caCert.__x;
			untyped __fiberus__("fib_ssl_conf_set_ca((FibSSLConfig*)", conf, ", (FibSSLCert*)", caPtr, ")");
		}

		/* Set verification mode */
		if (verifyCert == null)
			untyped __fiberus__("fib_ssl_conf_set_verify((FibSSLConfig*)", conf, ", 2)"); /* OPTIONAL */
		else if (verifyCert == true)
			untyped __fiberus__("fib_ssl_conf_set_verify((FibSSLConfig*)", conf, ", 1)"); /* REQUIRED */
		else
			untyped __fiberus__("fib_ssl_conf_set_verify((FibSSLConfig*)", conf, ", 0)"); /* NONE */

		return conf;
	}

	static function __init__():Void {
		DEFAULT_VERIFY_CERT = true;
		DEFAULT_CA = null;
		untyped __fiberus__("fib_ssl_init()");
	}
}

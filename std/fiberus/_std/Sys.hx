/*
 * Fiberus Sys - System functions implementation
 * 
 * Uses io_uring for non-blocking sleep and I/O operations.
 */

import fiberus.io.FD;
import fiberus.io.Timer;

@:coreApi
class Sys {
	static var _args:Array<String>;
	static var _stdin:haxe.io.Input;
	static var _stdout:haxe.io.Output;
	static var _stderr:haxe.io.Output;

	public static function print(v:Dynamic):Void {
		var s = Std.string(v);
		untyped __fiberus__("fib_print(", s, ")");
	}

	public static function println(v:Dynamic):Void {
		var s = Std.string(v);
		untyped __fiberus__("fib_println(", s, ")");
	}

	public static function args():Array<String> {
		if (_args == null)
			_args = [];
		return _args;
	}

	public static function command(cmd:String, ?args:Array<String>):Int {
		if (args == null) {
			return untyped __fiberus__("fib_sys_command(", cmd, ")");
		} else {
			return untyped __fiberus__("fib_sys_command_args(", cmd, ", ", args, ")");
		}
	}

	public static function cpuTime():Float {
		return untyped __fiberus__("(double)clock() / CLOCKS_PER_SEC");
	}

	public static function exit(code:Int):Void {
		untyped __fiberus__("exit(", code, ")");
	}

	public static function getChar(echo:Bool):Int {
		return untyped __fiberus__("getchar()");
	}

	public static function systemName():String {
		#if windows
		return "Windows";
		#elseif linux
		return "Linux";
		#elseif mac
		return "Mac";
		#else
		return "Unknown";
		#end
	}

	public static function environment():Map<String, String> {
		var result = new Map<String, String>();
		var vars:Array<String> = untyped __fiberus__("fib_sys_environment()");
		var i = 0;
		while (i < vars.length) {
			result.set(vars[i], vars[i + 1]);
			i += 2;
		}
		return result;
	}

	@:deprecated("Use programPath instead")
	public static function executablePath():String {
		return programPath();
	}

	public static function programPath():String {
		return untyped __fiberus__("fib_sys_program_path()");
	}

	public static function getCwd():String {
		return untyped __fiberus__("({ char* cwd = getcwd(NULL, 0); cwd ? fib_string_new(cwd) : NULL; })");
	}

	public static function setCwd(s:String):Void {
		untyped __fiberus__("chdir(fib_string_data(", s, "))");
	}

	public static function getEnv(s:String):Null<String> {
		return untyped __fiberus__("({ char* env = getenv(fib_string_data(", s, ")); env ? fib_string_new(env) : NULL; })");
	}

	public static function putEnv(s:String, v:Null<String>):Void {
		if (v == null) {
			untyped __fiberus__("unsetenv(fib_string_data(", s, "))");
		} else {
			untyped __fiberus__("setenv(fib_string_data(", s, "), fib_string_data(", v, "), 1)");
		}
	}

	public static function setTimeLocale(loc:String):Bool {
		return untyped __fiberus__("setlocale(LC_TIME, fib_string_data(", loc, ")) != NULL");
	}

	/**
	 * Sleep for the given number of seconds.
	 * Uses io_uring timeout - suspends the fiber without blocking the OS thread.
	 */
	public static function sleep(seconds:Float):Void {
		Timer.sleepSeconds(seconds);
	}

	/**
	 * Get standard error output stream.
	 */
	public static function stderr():haxe.io.Output {
		if (_stderr == null) _stderr = new StdOutput(2);
		return _stderr;
	}

	/**
	 * Get standard input stream.
	 */
	public static function stdin():haxe.io.Input {
		if (_stdin == null) _stdin = new StdInput(0);
		return _stdin;
	}

	/**
	 * Get standard output stream.
	 */
	public static function stdout():haxe.io.Output {
		if (_stdout == null) _stdout = new StdOutput(1);
		return _stdout;
	}

	public static function time():Float {
		return untyped __fiberus__("(double)time(NULL)");
	}
}

/**
 * Standard input stream wrapper.
 * Uses io_uring for non-blocking reads.
 */
private class StdInput extends haxe.io.Input {
	var fd:Int;
	
	public function new(fd:Int) {
		this.fd = fd;
	}
	
	override public function readByte():Int {
		var buf = haxe.io.Bytes.alloc(1);
		var n = FD.read(fd, buf, 0, 1);
		if (n <= 0) throw new haxe.io.Eof();
		return buf.get(0);
	}
	
	override public function readBytes(s:haxe.io.Bytes, pos:Int, len:Int):Int {
		if (len <= 0) return 0;
		var n = FD.read(fd, s, pos, len);
		if (n < 0) throw haxe.io.Error.Custom("Read error: errno " + (-n));
		if (n == 0) throw new haxe.io.Eof();
		return n;
	}
}

/**
 * Standard output stream wrapper.
 * Uses io_uring for non-blocking writes.
 */
private class StdOutput extends haxe.io.Output {
	var fd:Int;
	
	public function new(fd:Int) {
		this.fd = fd;
	}
	
	override public function writeByte(c:Int):Void {
		var buf = haxe.io.Bytes.alloc(1);
		buf.set(0, c);
		FD.write(fd, buf, 0, 1);
	}
	
	override public function writeBytes(s:haxe.io.Bytes, pos:Int, len:Int):Int {
		if (len <= 0) return 0;
		var n = FD.write(fd, s, pos, len);
		if (n < 0) throw haxe.io.Error.Custom("Write error: errno " + (-n));
		return n;
	}
	
	override public function flush():Void {
		FD.fsync(fd);
	}
}

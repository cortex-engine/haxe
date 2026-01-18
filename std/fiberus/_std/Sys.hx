/*
 * Fiberus Sys - System functions implementation
 */

@:coreApi
class Sys {
	static var _args:Array<String>;

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
		// TODO: Implement system command
		return -1;
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
		return new Map();
	}

	@:deprecated("Use programPath instead")
	public static function executablePath():String {
		return programPath();
	}

	public static function programPath():String {
		return "./";
	}

	public static function getCwd():String {
		return untyped __fiberus__("getcwd(NULL, 0)");
	}

	public static function setCwd(s:String):Void {
		untyped __fiberus__("chdir(fib_string_data(", s, "))");
	}

	public static function getEnv(s:String):Null<String> {
		var result = untyped __fiberus__("getenv(fib_string_data(", s, "))");
		if (result == null)
			return null;
		return untyped __fiberus__("fib_string_new(", result, ")");
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

	public static function sleep(seconds:Float):Void {
		untyped __fiberus__("usleep((useconds_t)(", seconds, " * 1000000))");
	}

	public static function stderr():haxe.io.Output {
		throw new haxe.exceptions.NotImplementedException();
	}

	public static function stdin():haxe.io.Input {
		throw new haxe.exceptions.NotImplementedException();
	}

	public static function stdout():haxe.io.Output {
		throw new haxe.exceptions.NotImplementedException();
	}

	public static function time():Float {
		return untyped __fiberus__("(double)time(NULL)");
	}
}

/*
 * Fiberus - sys.io.Process implementation
 *
 * Wraps the C-level FibProcess API (process.h/process.c) which uses
 * vendored subprocess.h for child process management with pipes.
 *
 * Pipe I/O is performed via read()/write() syscalls in GC-safe zones,
 * so blocking on pipe reads won't stall the GC stop-the-world.
 */

package sys.io;

import fiberus.FibProcessPtr;

private class ProcessInput extends haxe.io.Input {
	var proc:FibProcessPtr;
	var isStdout:Bool;

	public function new(proc:FibProcessPtr, isStdout:Bool) {
		this.proc = proc;
		this.isStdout = isStdout;
	}

	override public function readByte():Int {
		var buf = haxe.io.Bytes.alloc(1);
		var n = readBytes(buf, 0, 1);
		if (n == 0)
			throw new haxe.io.Eof();
		return buf.get(0);
	}

	override public function readBytes(s:haxe.io.Bytes, pos:Int, len:Int):Int {
		if (len <= 0)
			return 0;

		var data = s.getData();
		var result:Int;
		if (isStdout) {
			result = untyped __fiberus__("fib_process_read_stdout(", proc, ", (char*)fib_bytes_data(", data, ") + ", pos, ", ", len, ")");
		} else {
			result = untyped __fiberus__("fib_process_read_stderr(", proc, ", (char*)fib_bytes_data(", data, ") + ", pos, ", ", len, ")");
		}

		if (result < 0)
			throw new haxe.io.Eof();
		if (result == 0)
			throw new haxe.io.Eof();
		return result;
	}
}

private class ProcessOutput extends haxe.io.Output {
	var proc:FibProcessPtr;

	public function new(proc:FibProcessPtr) {
		this.proc = proc;
	}

	override public function close():Void {
		untyped __fiberus__("fib_process_close_stdin(", proc, ")");
	}

	override public function writeByte(c:Int):Void {
		var buf = haxe.io.Bytes.alloc(1);
		buf.set(0, c);
		writeBytes(buf, 0, 1);
	}

	override public function writeBytes(s:haxe.io.Bytes, pos:Int, len:Int):Int {
		if (len <= 0)
			return 0;

		var data = s.getData();
		var result:Int = untyped __fiberus__("fib_process_write_stdin(", proc, ", (const char*)fib_bytes_data(", data, ") + ", pos, ", ", len, ")");

		if (result < 0)
			throw new haxe.io.Eof();
		return result;
	}
}

@:coreApi
class Process {
	var proc:FibProcessPtr;

	public var stdout(default, null):haxe.io.Input;
	public var stderr(default, null):haxe.io.Input;
	public var stdin(default, null):haxe.io.Output;

	public function new(cmd:String, ?args:Array<String>, ?detached:Bool):Void {
		if (detached == true)
			throw "Detached process is not supported on this platform";

		if (args != null) {
			proc = untyped __fiberus__("fib_process_create(", cmd, ", ", args, ")");
		} else {
			proc = untyped __fiberus__("fib_process_create(", cmd, ", NULL)");
		}

		var isNull:Bool = untyped __fiberus__("(", proc, " == NULL)");
		if (isNull)
			throw "Process creation failure : " + cmd;

		var stdinStream:haxe.io.Output = new ProcessOutput(proc);
		var stdoutStream:haxe.io.Input = new ProcessInput(proc, true);
		var stderrStream:haxe.io.Input = new ProcessInput(proc, false);
		stdin = stdinStream;
		stdout = stdoutStream;
		stderr = stderrStream;
	}

	public function getPid():Int {
		return untyped __fiberus__("fib_process_pid(", proc, ")");
	}

	public function exitCode(block:Bool = true):Null<Int> {
		if (block) {
			var code:Int = untyped __fiberus__("fib_process_exit_code(", proc, ", 1)");
			return code;
		} else {
			var code:Int = untyped __fiberus__("fib_process_exit_code(", proc, ", 0)");
			var exited:Bool = untyped __fiberus__("(", proc, "->exited)");
			if (!exited)
				return null;
			return code;
		}
	}

	public function close():Void {
		untyped __fiberus__("fib_process_close(", proc, ")");
	}

	public function kill():Void {
		untyped __fiberus__("fib_process_kill(", proc, ")");
	}
}

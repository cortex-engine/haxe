/*
 * Copyright (C)2005-2019 Haxe Foundation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

package haxe.zip;

import haxe.io.Bytes;

/**
 * Fiberus Compress implementation backed by miniz (via compress.h/compress.c).
 *
 * Provides streaming deflate compression and a one-shot static run() helper.
 * Uses __fiberus__() intrinsics to call C wrapper functions.
 */
@:coreApi class Compress {
	var c:fiberus.FibCompressPtr;

	public function new(level:Int) {
		c = untyped __fiberus__("fib_compress_new(", level, ")");
	}

	public function execute(src:Bytes, srcPos:Int, dst:Bytes, dstPos:Int):{done:Bool, read:Int, write:Int} {
		var srcData = src.getData();
		var dstData = dst.getData();
		var srcLen = src.length - srcPos;
		var dstLen = dst.length - dstPos;
		untyped __fiberus__("fib_compress_execute(", c, ", ", srcData, ", ", srcPos, ", ", srcLen, ", ", dstData, ", ", dstPos, ", ", dstLen, ")");
		var done:Bool = untyped __fiberus__("(bool)", c, "->result_done");
		var read:Int = untyped __fiberus__(c, "->result_read");
		var write:Int = untyped __fiberus__(c, "->result_write");
		return {done: done, read: read, write: write};
	}

	public function setFlushMode(f:FlushMode):Void {
		var mode:Int = switch (f) {
			case NO: 0;
			case SYNC: 2;
			case FULL: 3;
			case FINISH: 4;
			case BLOCK: 5;
		};
		untyped __fiberus__("fib_compress_set_flush(", c, ", ", mode, ")");
	}

	public function close():Void {
		untyped __fiberus__("fib_compress_close(", c, ")");
	}

	public static function run(s:Bytes, level:Int):Bytes {
		var srcData = s.getData();
		var srcLen = s.length;
		var resultData:haxe.io.BytesData = untyped __fiberus__("fib_compress_run(", srcData, ", ", srcLen, ", ", level, ")");
		return Bytes.ofData(resultData);
	}
}

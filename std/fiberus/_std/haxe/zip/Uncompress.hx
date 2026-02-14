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
 * Fiberus Uncompress implementation backed by miniz (via compress.h/compress.c).
 *
 * Provides streaming inflate decompression and a one-shot static run() helper.
 * Uses __fiberus__() intrinsics to call C wrapper functions.
 */
@:coreApi class Uncompress {
	var u:fiberus.FibUncompressPtr;

	public function new(?windowBits:Int) {
		var wb:Int = windowBits != null ? (windowBits : Int) : 15;
		u = untyped __fiberus__("fib_uncompress_new(", wb, ")");
	}

	public function execute(src:Bytes, srcPos:Int, dst:Bytes, dstPos:Int):{done:Bool, read:Int, write:Int} {
		var srcData = src.getData();
		var dstData = dst.getData();
		var srcLen = src.length - srcPos;
		var dstLen = dst.length - dstPos;
		untyped __fiberus__("fib_uncompress_execute(", u, ", ", srcData, ", ", srcPos, ", ", srcLen, ", ", dstData, ", ", dstPos, ", ", dstLen, ")");
		var done:Bool = untyped __fiberus__("(bool)", u, "->result_done");
		var read:Int = untyped __fiberus__(u, "->result_read");
		var write:Int = untyped __fiberus__(u, "->result_write");
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
		untyped __fiberus__("fib_uncompress_set_flush(", u, ", ", mode, ")");
	}

	public function close():Void {
		untyped __fiberus__("fib_uncompress_close(", u, ")");
	}

	public static function run(src:Bytes, ?bufsize:Int):Bytes {
		var srcData = src.getData();
		var srcLen = src.length;
		var bs:Int = bufsize != null ? (bufsize : Int) : 0;
		var resultData:haxe.io.BytesData = untyped __fiberus__("fib_uncompress_run(", srcData, ", ", srcLen, ", ", bs, ")");
		return Bytes.ofData(resultData);
	}
}

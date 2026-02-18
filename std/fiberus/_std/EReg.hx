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

/**
 * Fiberus EReg implementation backed by pcre2 (via ereg.h/ereg.c).
 *
 * Architecture follows hxcpp: 5 C primitives via __fiberus__() intrinsics,
 * pure Haxe for split/replace/map/escape/matchedLeft/matchedRight.
 *
 * The 'g' (global) modifier is handled at the Haxe level only, as pcre2
 * has no concept of global matching.
 */
@:coreApi class EReg {
	var r:fiberus.FibERegPtr;
	var last:String;
	var global:Bool;

	public function new(r:String, opt:String):Void {
		var a = opt.split("g");
		global = a.length > 1;
		if (global)
			opt = a.join("");
		this.r = untyped __fiberus__("fib_ereg_new(", r, ", ", opt, ")");
	}

	public function match(s:String):Bool {
		var p:Bool = untyped __fiberus__("fib_ereg_match(", r, ", ", s, ", 0, -1)");
		if (p)
			last = s;
		else
			last = null;
		return p;
	}

	public function matched(n:Int):String {
		if (last == null) throw "EReg::matched";
		var ncaptures:Int = untyped __fiberus__("fib_ereg_capture_count(", r, ")");
		if (n < 0 || n >= ncaptures) throw "EReg::matched";
		return untyped __fiberus__("fib_ereg_matched(", r, ", ", n, ")");
	}

	public function matchedLeft():String {
		var p = matchedPos();
		return last.substr(0, p.pos);
	}

	public function matchedRight():String {
		var p = matchedPos();
		var sz = p.pos + p.len;
		return last.substr(sz, last.length - sz);
	}

	public function matchedPos():{pos:Int, len:Int} {
		var pos:Int = untyped __fiberus__("fib_ereg_matched_start(", r, ", 0)");
		var len:Int = untyped __fiberus__("fib_ereg_matched_len(", r, ", 0)");
		return {pos: pos, len: len};
	}

	public function matchSub(s:String, pos:Int, len:Int = -1):Bool {
		var effLen = len < 0 ? s.length - pos : len;
		var p:Bool = untyped __fiberus__("fib_ereg_match(", r, ", ", s, ", ", pos, ", ", effLen, ")");
		if (p)
			last = s;
		else
			last = null;
		return p;
	}

	public function matchedNum():Int {
		var num:Int = untyped __fiberus__("fib_ereg_matched_num(", r, ")");
		if (num == -1)
			return 0;
		return num;
	}

	public function split(s:String):Array<String> {
		var pos = 0;
		var len = s.length;
		var a = new Array<String>();
		var first = true;
		do {
			var effLen = len;
			var matched:Bool = untyped __fiberus__("fib_ereg_match(", r, ", ", s, ", ", pos, ", ", effLen, ")");
			if (!matched)
				break;
			var mpos:Int = untyped __fiberus__("fib_ereg_matched_start(", r, ", 0)");
			var mlen:Int = untyped __fiberus__("fib_ereg_matched_len(", r, ", 0)");
			if (mlen == 0 && !first) {
				if (mpos == s.length)
					break;
				mpos += 1;
			}
			a.push(s.substr(pos, mpos - pos));
			var tot = mpos + mlen - pos;
			pos += tot;
			len -= tot;
			first = false;
		} while (global);
		a.push(s.substr(pos, len));
		return a;
	}

	public function replace(s:String, by:String):String {
		var b = new StringBuf();
		var pos = 0;
		var len = s.length;
		var a = by.split("$");
		var first = true;
		do {
			var effLen = len;
			var matched:Bool = untyped __fiberus__("fib_ereg_match(", r, ", ", s, ", ", pos, ", ", effLen, ")");
			if (!matched)
				break;
			var mpos:Int = untyped __fiberus__("fib_ereg_matched_start(", r, ", 0)");
			var mlen:Int = untyped __fiberus__("fib_ereg_matched_len(", r, ", 0)");
			if (mlen == 0 && !first) {
				if (mpos == s.length)
					break;
				mpos += 1;
			}
			b.addSub(s, pos, mpos - pos);
			if (a.length > 0)
				b.add(a[0]);
			var i = 1;
			while (i < a.length) {
				var k = a[i];
				// Check if k is empty (charCodeAt returns Null<Int> which codegen
				// wraps in fib_dynamic_int, losing the null — use length check instead)
				if (k.length == 0) {
					// Empty string between $$ — emit literal $
					b.add("$");
					i++;
					var k2 = a[i];
					if (k2 != null && k2.length > 0)
						b.add(k2);
				} else {
					var c = k.charCodeAt(0);
					// 1...9
					if (c >= 49 && c <= 57) {
						var gn = c - 48;
						var gpos:Int = untyped __fiberus__("fib_ereg_matched_start(", r, ", ", gn, ")");
						if (gpos < 0) {
							b.add("$");
							b.add(k);
						} else {
							var glen:Int = untyped __fiberus__("fib_ereg_matched_len(", r, ", ", gn, ")");
							b.addSub(s, gpos, glen);
							b.addSub(k, 1, k.length - 1);
						}
					} else {
						b.add("$");
						b.add(k);
					}
				}
				i++;
			}
			var tot = mpos + mlen - pos;
			pos += tot;
			len -= tot;
			first = false;
		} while (global);
		b.addSub(s, pos, len);
		return b.toString();
	}

	public function map(s:String, f:EReg->String):String {
		var offset = 0;
		var buf = new StringBuf();
		do {
			if (offset >= s.length)
				break;
			else if (!matchSub(s, offset, -1)) {
				buf.add(s.substr(offset));
				break;
			}
			var mpos:Int = untyped __fiberus__("fib_ereg_matched_start(", r, ", 0)");
			var mlen:Int = untyped __fiberus__("fib_ereg_matched_len(", r, ", 0)");
			buf.add(s.substr(offset, mpos - offset));
			buf.add(f(this));
			if (mlen == 0) {
				buf.add(s.substr(mpos, 1));
				offset = mpos + 1;
			} else
				offset = mpos + mlen;
		} while (global);
		if (!global && offset > 0 && offset < s.length)
			buf.add(s.substr(offset));
		return buf.toString();
	}

	public static function escape(s:String):String {
		return escapeRegExpRe.map(s, function(r) return "\\" + r.matched(0));
	}

	static var escapeRegExpRe = ~/[\[\]{}()*+?.\\\^$|]/g;

	function toString():String
		return 'EReg($r)';
}

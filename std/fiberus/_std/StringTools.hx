/*
 * Fiberus StringTools override
 *
 * Only overrides fastCodeAt/unsafeCodeAt/isEof to use fib_string_char_code_at
 * instead of the default `s.cca(index)` which generates broken dynamic dispatch.
 * fastCodeAt/unsafeCodeAt return 0 for out-of-bounds (matching cpp/hl behavior).
 */

import haxe.iterators.StringIterator;
import haxe.iterators.StringKeyValueIterator;

@:coreApi class StringTools {
	public static function urlEncode(s:String):String {
		var buf = new StringBuf();
		var i = 0;
		var len = s.length;
		while (i < len) {
			var c = s.charCodeAt(i);
			if (c == null) break;
			var code:Int = c;
			if ((code >= 0x41 && code <= 0x5A) || // A-Z
				(code >= 0x61 && code <= 0x7A) || // a-z
				(code >= 0x30 && code <= 0x39) || // 0-9
				code == 0x2D || code == 0x5F || code == 0x2E || code == 0x7E) { // -_.~
				buf.addChar(code);
			} else if (code == 0x20) {
				buf.add("%20");
			} else if (code < 0x80) {
				buf.add("%" + hex(code, 2));
			} else {
				// Encode codepoint to UTF-8 bytes, then percent-encode each byte
				if (code < 0x800) {
					buf.add("%" + hex(0xC0 | (code >> 6), 2));
					buf.add("%" + hex(0x80 | (code & 0x3F), 2));
				} else if (code < 0x10000) {
					buf.add("%" + hex(0xE0 | (code >> 12), 2));
					buf.add("%" + hex(0x80 | ((code >> 6) & 0x3F), 2));
					buf.add("%" + hex(0x80 | (code & 0x3F), 2));
				} else {
					buf.add("%" + hex(0xF0 | (code >> 18), 2));
					buf.add("%" + hex(0x80 | ((code >> 12) & 0x3F), 2));
					buf.add("%" + hex(0x80 | ((code >> 6) & 0x3F), 2));
					buf.add("%" + hex(0x80 | (code & 0x3F), 2));
				}
			}
			i++;
		}
		return buf.toString();
	}

	public static function urlDecode(s:String):String {
		var buf = new StringBuf();
		var i = 0;
		var len = s.length;
		while (i < len) {
			var c = s.charCodeAt(i);
			if (c == null) break;
			var code:Int = c;
			if (code == 0x25 && i + 2 < len) { // %
				var h1 = s.charCodeAt(i + 1);
				var h2 = s.charCodeAt(i + 2);
				if (h1 != null && h2 != null) {
					var hi:Int = hexVal(h1);
					var lo:Int = hexVal(h2);
					if (hi >= 0 && lo >= 0) {
						var b0 = hi * 16 + lo;
						if (b0 < 0x80) {
							// ASCII byte — emit directly
							buf.addChar(b0);
						} else {
							// UTF-8 multi-byte: determine sequence length from lead byte
							var cp = 0;
							var seqLen = 0;
							if ((b0 & 0xE0) == 0xC0) { cp = b0 & 0x1F; seqLen = 2; }
							else if ((b0 & 0xF0) == 0xE0) { cp = b0 & 0x0F; seqLen = 3; }
							else if ((b0 & 0xF8) == 0xF0) { cp = b0 & 0x07; seqLen = 4; }
							else { buf.addChar(b0); i += 3; continue; } // invalid lead, emit as-is
							var ok = true;
							var j = 1;
							var ni = i + 3; // position after first %XX
							while (j < seqLen) {
								if (ni + 2 < len && s.charCodeAt(ni) == 0x25) {
									var ch1 = s.charCodeAt(ni + 1);
									var ch2 = s.charCodeAt(ni + 2);
									if (ch1 != null && ch2 != null) {
										var hv:Int = hexVal(ch1);
										var lv:Int = hexVal(ch2);
										if (hv >= 0 && lv >= 0) {
											var cont = hv * 16 + lv;
											if ((cont & 0xC0) == 0x80) {
												cp = (cp << 6) | (cont & 0x3F);
												ni += 3;
												j++;
												continue;
											}
										}
									}
								}
								// Continuation byte missing/invalid — emit lead as-is
								ok = false;
								break;
							}
							if (ok) {
								buf.addChar(cp);
								i = ni;
								continue;
							} else {
								buf.addChar(b0);
							}
						}
						i += 3;
						continue;
					}
				}
			} else if (code == 0x2B) { // +
				buf.addChar(0x20);
				i++;
				continue;
			}
			buf.addChar(code);
			i++;
		}
		return buf.toString();
	}

	static function hexVal(c:Null<Int>):Int {
		if (c == null) return -1;
		var code:Int = c;
		if (code >= 0x30 && code <= 0x39) return code - 0x30;
		if (code >= 0x41 && code <= 0x46) return code - 0x41 + 10;
		if (code >= 0x61 && code <= 0x66) return code - 0x61 + 10;
		return -1;
	}

	public static function htmlEscape(s:String, quotes:Bool = false):String {
		var buf = new StringBuf();
		var i = 0;
		var len = s.length;
		while (i < len) {
			var c = s.charCodeAt(i);
			if (c == null) break;
			var code:Int = c;
			if (code == 0x26) buf.add("&amp;")
			else if (code == 0x3C) buf.add("&lt;")
			else if (code == 0x3E) buf.add("&gt;")
			else if (quotes && code == 0x22) buf.add("&quot;")
			else if (quotes && code == 0x27) buf.add("&#039;")
			else buf.addChar(code);
			i++;
		}
		return buf.toString();
	}

	public static function htmlUnescape(s:String):String {
		return s.split("&gt;").join(">").split("&lt;").join("<").split("&quot;").join('"').split("&#039;").join("'").split("&amp;").join("&");
	}

	public static inline function contains(s:String, value:String):Bool {
		return s.indexOf(value) != -1;
	}

	public static function startsWith(s:String, start:String):Bool {
		if (start.length == 0) return true;
		if (s.length < start.length) return false;
		return s.substr(0, start.length) == start;
	}

	public static function endsWith(s:String, end:String):Bool {
		var elen = end.length;
		if (elen == 0) return true;
		var slen = s.length;
		if (slen < elen) return false;
		return s.substr(slen - elen) == end;
	}

	public static function isSpace(s:String, pos:Int):Bool {
		var c = s.charCodeAt(pos);
		if (c == null) return false;
		var code:Int = c;
		return (code >= 9 && code <= 13) || code == 32;
	}

	public static function ltrim(s:String):String {
		var l = s.length;
		var r = 0;
		while (r < l && isSpace(s, r))
			r++;
		if (r > 0)
			return s.substr(r, l - r);
		else
			return s;
	}

	public static function rtrim(s:String):String {
		var l = s.length;
		var r = 0;
		while (r < l && isSpace(s, l - r - 1))
			r++;
		if (r > 0)
			return s.substr(0, l - r);
		else
			return s;
	}

	public static inline function trim(s:String):String {
		return ltrim(rtrim(s));
	}

	public static function rpad(s:String, c:String, l:Int):String {
		if (c.length == 0) return s;
		var buf = new StringBuf();
		buf.add(s);
		while (buf.length < l)
			buf.add(c);
		return buf.toString();
	}

	public static function lpad(s:String, c:String, l:Int):String {
		if (c.length == 0) return s;
		var buf = new StringBuf();
		var needed = l - s.length;
		while (buf.length < needed)
			buf.add(c);
		buf.add(s);
		return buf.toString();
	}

	public static function replace(s:String, sub:String, by:String):String {
		return s.split(sub).join(by);
	}

	public static function hex(n:Int, ?digits:Int):String {
		var s:String = "";
		var hexChars = "0123456789ABCDEF";
		do {
			s = hexChars.charAt(n & 15) + s;
			n = n >>> 4;
		} while (n > 0);
		if (digits != null) {
			while (s.length < digits)
				s = "0" + s;
		}
		return s;
	}

	/**
	 * Fast character code access. Returns codepoint at index, or 0 for out-of-bounds.
	 * charCodeAt returns Null<Int> (null for OOB), so we convert null to 0 here
	 * to match cpp/hl behavior where isEof(0) == true.
	 */
	public static inline function fastCodeAt(s:String, index:Int):Int {
		var c = s.charCodeAt(index);
		return c != null ? (c : Int) : 0;
	}

	/**
	 * Unsafe (no bounds checking) character code access.
	 * Same as fastCodeAt on Fiberus.
	 */
	public static inline function unsafeCodeAt(s:String, index:Int):Int {
		var c = s.charCodeAt(index);
		return c != null ? (c : Int) : 0;
	}

	public static inline function iterator(s:String):StringIterator {
		return new StringIterator(s);
	}

	public static inline function keyValueIterator(s:String):StringKeyValueIterator {
		return new StringKeyValueIterator(s);
	}

	/**
	 * Check for end-of-file. Returns true for 0 (matching cpp/hl behavior).
	 */
	@:noUsing public static inline function isEof(c:Int):Bool {
		return c == 0;
	}

	@:noCompletion
	@:deprecated('StringTools.quoteUnixArg() is deprecated. Use haxe.SysTools.quoteUnixArg() instead.')
	public static function quoteUnixArg(argument:String):String {
		return inline haxe.SysTools.quoteUnixArg(argument);
	}

	@:noCompletion
	@:deprecated('StringTools.winMetaCharacters is deprecated. Use haxe.SysTools.winMetaCharacters instead.')
	public static var winMetaCharacters:Array<Int> = cast haxe.SysTools.winMetaCharacters;

	@:noCompletion
	@:deprecated('StringTools.quoteWinArg() is deprecated. Use haxe.SysTools.quoteWinArg() instead.')
	public static function quoteWinArg(argument:String, escapeMetaCharacters:Bool):String {
		return inline haxe.SysTools.quoteWinArg(argument, escapeMetaCharacters);
	}
}

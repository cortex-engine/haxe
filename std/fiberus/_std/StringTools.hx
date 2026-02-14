/*
 * Fiberus StringTools override
 *
 * Only overrides fastCodeAt/unsafeCodeAt/isEof to use fib_string_char_code_at
 * instead of the default `s.cca(index)` which generates broken dynamic dispatch.
 * fib_string_char_code_at returns -1 for out-of-bounds (same as Java/Python).
 */

import haxe.iterators.StringIterator;
import haxe.iterators.StringKeyValueIterator;

@:coreApi class StringTools {
	public static function urlEncode(s:String):String {
		// Use pure-Haxe fallback — encode each non-alphanum char
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
			} else {
				buf.add("%" + hex(code, 2));
			}
			i++;
		}
		return buf.toString();
	}

	public static function urlDecode(s:String):String {
		// Simple implementation — delegate to percent-decode
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
						buf.addChar(hi * 16 + lo);
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
	 * Fast character code access. Uses fib_string_char_code_at which returns -1
	 * for out-of-bounds. This is the Fiberus equivalent of s.cca(index).
	 */
	public static inline function fastCodeAt(s:String, index:Int):Int {
		return untyped __fiberus__("fib_string_char_code_at(", s, ", ", index, ")");
	}

	/**
	 * Unsafe (no bounds checking) character code access.
	 * Same as fastCodeAt on Fiberus since fib_string_char_code_at handles bounds.
	 */
	public static inline function unsafeCodeAt(s:String, index:Int):Int {
		return untyped __fiberus__("fib_string_char_code_at(", s, ", ", index, ")");
	}

	public static inline function iterator(s:String):StringIterator {
		return new StringIterator(s);
	}

	public static inline function keyValueIterator(s:String):StringKeyValueIterator {
		return new StringKeyValueIterator(s);
	}

	/**
	 * Check for end-of-file. fib_string_char_code_at returns -1 for out-of-bounds.
	 */
	@:noUsing public static inline function isEof(c:Int):Bool {
		return c == -1;
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

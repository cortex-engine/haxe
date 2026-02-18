/*
 * Fiberus - Efficient Bytes implementation using native byte arrays
 *
 * This replaces the default per-byte-iteration implementation with
 * native memset/memcpy/memcmp operations for optimal performance.
 */
package haxe.io;

class Bytes {
	public var length(default, null):Int;

	final b:BytesData;

	inline function new(length:Int, b:BytesData) {
		this.length = length;
		this.b = b;
	}

	public inline function get(pos:Int):Int {
		return untyped __fiberus__("fib_bytes_get(", b, ", ", pos, ")");
	}

	public inline function set(pos:Int, v:Int):Void {
		untyped __fiberus__("fib_bytes_set(", b, ", ", pos, ", (uint8_t)", v, ")");
	}

	public function blit(pos:Int, src:Bytes, srcpos:Int, len:Int):Void {
		if (pos < 0 || srcpos < 0 || len < 0 || pos + len > length || srcpos + len > src.length)
			throw Error.OutsideBounds;
		untyped __fiberus__("fib_bytes_blit(", src.b, ", ", srcpos, ", ", b, ", ", pos, ", ", len, ")");
	}

	public function fill(pos:Int, len:Int, value:Int):Void {
		if (pos < 0 || len < 0 || pos + len > length)
			throw Error.OutsideBounds;
		untyped __fiberus__("fib_bytes_fill(", b, ", ", pos, ", ", len, ", (uint8_t)", value, ")");
	}

	public function sub(pos:Int, len:Int):Bytes {
		if (pos < 0 || len < 0 || pos + len > length)
			throw Error.OutsideBounds;
		var newData:BytesData = untyped __fiberus__("fib_bytes_sub(", b, ", ", pos, ", ", len, ")");
		return new Bytes(len, newData);
	}

	public inline function compare(other:Bytes):Int {
		return untyped __fiberus__("fib_bytes_compare(", b, ", ", other.b, ")");
	}

	public function getDouble(pos:Int):Float {
		return untyped __fiberus__("fib_bytes_get_double(", b, ", ", pos, ")");
	}

	public function getFloat(pos:Int):Float {
		return untyped __fiberus__("fib_bytes_get_float(", b, ", ", pos, ")");
	}

	public function setDouble(pos:Int, v:Float):Void {
		untyped __fiberus__("fib_bytes_set_double(", b, ", ", pos, ", ", v, ")");
	}

	public function setFloat(pos:Int, v:Float):Void {
		untyped __fiberus__("fib_bytes_set_float(", b, ", ", pos, ", ", v, ")");
	}

	public function getUInt16(pos:Int):Int {
		return untyped __fiberus__("((int32_t)fib_bytes_get_int16(", b, ", ", pos, ") & 0xFFFF)");
	}

	public function setUInt16(pos:Int, v:Int):Void {
		untyped __fiberus__("fib_bytes_set_int16(", b, ", ", pos, ", (int16_t)", v, ")");
	}

	public function getInt32(pos:Int):Int {
		return untyped __fiberus__("fib_bytes_get_int32(", b, ", ", pos, ")");
	}

	public function getInt64(pos:Int):haxe.Int64 {
		var low = getInt32(pos);
		var high = getInt32(pos + 4);
		return haxe.Int64.make(high, low);
	}

	public function setInt32(pos:Int, v:Int):Void {
		untyped __fiberus__("fib_bytes_set_int32(", b, ", ", pos, ", ", v, ")");
	}

	public function setInt64(pos:Int, v:haxe.Int64):Void {
		setInt32(pos, v.low);
		setInt32(pos + 4, v.high);
	}

	public function getString(pos:Int, len:Int, ?encoding:Encoding):String {
		if (pos < 0 || len < 0 || pos + len > length)
			throw Error.OutsideBounds;
		if (len == 0) return "";
		var subData:BytesData = untyped __fiberus__("fib_bytes_sub(", b, ", ", pos, ", ", len, ")");
		return untyped __fiberus__("fib_bytes_to_string(", subData, ")");
	}

	@:deprecated("readString is deprecated, use getString instead")
	@:noCompletion
	public inline function readString(pos:Int, len:Int):String {
		return getString(pos, len);
	}

	public inline function toString():String {
		return getString(0, length);
	}

	public function toHex():String {
		var s = new StringBuf();
		var chars = "0123456789abcdef";
		for (i in 0...length) {
			var c = get(i);
			s.addChar(chars.charCodeAt(c >> 4));
			s.addChar(chars.charCodeAt(c & 15));
		}
		return s.toString();
	}

	public inline function getData():BytesData {
		return b;
	}

	public static inline function alloc(length:Int):Bytes {
		var data:BytesData = untyped __fiberus__("fib_bytes_alloc(", length, ")");
		return new Bytes(length, data);
	}

	public static function ofString(s:String, ?encoding:Encoding):Bytes {
		var data:BytesData = untyped __fiberus__("fib_bytes_of_string(", s, ")");
		var len:Int = untyped __fiberus__("fib_bytes_length(", data, ")");
		return new Bytes(len, data);
	}

	public static function ofData(b:BytesData):Bytes {
		// Use direct pointer check via __fiberus__ since BytesData is native pointer
		var isNull:Bool = untyped __fiberus__("(", b, " == NULL)");
		if (isNull) {
			// Return empty Bytes if BytesData is null
			return alloc(0);
		}
		var len:Int = untyped __fiberus__("fib_bytes_length(", b, ")");
		return new Bytes(len, b);
	}

	public static function ofHex(s:String):Bytes {
		if ((s.length & 1) != 0) {
			throw "Not a hex string (odd number of digits)";
		}
		var output = Bytes.alloc(s.length >> 1);
		for (i in 0...output.length) {
			var highCode = StringTools.fastCodeAt(s, i * 2);
			var lowCode = StringTools.fastCodeAt(s, i * 2 + 1);
			var high = (highCode & 0xF) + ((highCode & 0x40) >> 6) * 9;
			var low = (lowCode & 0xF) + ((lowCode & 0x40) >> 6) * 9;
			output.set(i, ((high << 4) | low) & 0xFF);
		}
		return output;
	}

	public static inline function fastGet(b:BytesData, pos:Int):Int {
		return untyped __fiberus__("fib_bytes_get(", b, ", ", pos, ")");
	}
}

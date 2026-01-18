/*
 * Fiberus BytesBuffer implementation
 * Uses native BytesData for efficient byte buffer operations
 */
package haxe.io;

class BytesBuffer {
	var b:BytesData;

	public var length(get, never):Int;

	public function new() {
		b = untyped __fiberus__("fib_bytes_alloc(0)");
	}

	inline function get_length():Int {
		return b.length;
	}

	public inline function addByte(byte:Int):Void {
		b.push(byte);
	}

	public inline function add(src:Bytes):Void {
		var b2 = src.getData();
		for (i in 0...src.length)
			b.push(b2[i]);
	}

	public inline function addString(v:String, ?encoding:Encoding):Void {
		add(Bytes.ofString(v, encoding));
	}

	public function addInt32(v:Int):Void {
		addByte(v & 0xFF);
		addByte((v >> 8) & 0xFF);
		addByte((v >> 16) & 0xFF);
		addByte(v >>> 24);
	}

	public function addInt64(v:haxe.Int64):Void {
		addInt32(v.low);
		addInt32(v.high);
	}

	public inline function addFloat(v:Float):Void {
		addInt32(FPHelper.floatToI32(v));
	}

	public inline function addDouble(v:Float):Void {
		addInt64(FPHelper.doubleToI64(v));
	}

	public function addBytes(src:Bytes, pos:Int, len:Int):Void {
		if (pos < 0 || len < 0 || pos + len > src.length)
			throw Error.OutsideBounds;

		var b2 = src.getData();
		for (i in pos...pos + len)
			b.push(b2[i]);
	}

	public function getBytes():Bytes {
		var bytes = Bytes.ofData(b);
		b = null;
		return bytes;
	}
}

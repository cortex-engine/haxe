/*
 * Fiberus BytesData implementation
 * Native byte array wrapper with array access support
 */
package haxe.io;

/* BytesData as abstract over native pointer for array access support */
@:native("FibBytesData*")
abstract BytesData(Dynamic) {
	/* Array access support for standard library compatibility */
	@:arrayAccess public inline function arrayGet(index:Int):Int {
		return untyped __fiberus__("fib_bytes_get(", this, ", ", index, ")");
	}

	@:arrayAccess public inline function arraySet(index:Int, value:Int):Int {
		untyped __fiberus__("fib_bytes_set(", this, ", ", index, ", (uint8_t)", value, ")");
		return value;
	}

	public var length(get, never):Int;
	inline function get_length():Int {
		return untyped __fiberus__("((FibBytesData*)", this, ")->length");
	}

	/* Push for BytesBuffer compatibility - appends byte to buffer */
	public inline function push(value:Int):Void {
		untyped __fiberus__("fib_bytes_push(", this, ", (uint8_t)", value, ")");
	}
}

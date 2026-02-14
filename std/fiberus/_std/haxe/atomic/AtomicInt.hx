package haxe.atomic;

private final class Data {
	public var value:Int;

	public function new(value:Int) {
		this.value = value;
	}
}

abstract AtomicInt(Data) {
	public inline function new(value:Int) {
		this = new Data(value);
	}

	public inline function add(b:Int):Int {
		return untyped __fiberus__("fib_atomic_int_add(&", this.value, ",", b, ")");
	}

	public inline function sub(b:Int):Int {
		return untyped __fiberus__("fib_atomic_int_sub(&", this.value, ",", b, ")");
	}

	public inline function and(b:Int):Int {
		return untyped __fiberus__("fib_atomic_int_and(&", this.value, ",", b, ")");
	}

	public inline function or(b:Int):Int {
		return untyped __fiberus__("fib_atomic_int_or(&", this.value, ",", b, ")");
	}

	public inline function xor(b:Int):Int {
		return untyped __fiberus__("fib_atomic_int_xor(&", this.value, ",", b, ")");
	}

	public inline function compareExchange(expected:Int, replacement:Int):Int {
		return untyped __fiberus__("fib_atomic_int_compare_exchange(&", this.value, ",", expected, ",", replacement, ")");
	}

	public inline function exchange(value:Int):Int {
		return untyped __fiberus__("fib_atomic_int_exchange(&", this.value, ",", value, ")");
	}

	public inline function load():Int {
		return untyped __fiberus__("fib_atomic_int_load(&", this.value, ")");
	}

	public inline function store(value:Int):Int {
		return untyped __fiberus__("fib_atomic_int_store(&", this.value, ",", value, ")");
	}
}

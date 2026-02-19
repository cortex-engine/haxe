package haxe.atomic;

private final class ObjectData {
	public var ptr:haxe.Int64;

	public function new(value:haxe.Int64) {
		this.ptr = value;
	}
}

abstract AtomicObject<T:{}>(ObjectData) {
	public inline function new(value:T) {
		var v:T = value;
		this = new ObjectData(untyped __fiberus__("(int64_t)(void*)", v));
	}

	public inline function compareExchange(expected:T, replacement:T):T {
		var e:T = expected;
		var r:T = replacement;
		return untyped __fiberus__("(void*)fib_atomic_obj_compare_exchange((void**)&", this.ptr, ",(void*)", e, ",(void*)", r, ")");
	}

	public inline function exchange(value:T):T {
		var v:T = value;
		return untyped __fiberus__("(void*)fib_atomic_ptr_exchange((void**)&", this.ptr, ",(void*)", v, ")");
	}

	public inline function load():T {
		return untyped __fiberus__("(void*)fib_atomic_ptr_load((void**)&", this.ptr, ")");
	}

	public inline function store(value:T):T {
		var v:T = value;
		return untyped __fiberus__("(void*)fib_atomic_ptr_store((void**)&", this.ptr, ",(void*)", v, ")");
	}
}

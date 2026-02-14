package haxe.atomic;

private final class ObjectData {
	public var ptr:haxe.Int64;

	public function new(value:haxe.Int64) {
		this.ptr = value;
	}
}

abstract AtomicObject<T:{}>(ObjectData) {
	public inline function new(value:T) {
		this = new ObjectData(untyped __fiberus__("(int64_t)(void*)", value));
	}

	public inline function compareExchange(expected:T, replacement:T):T {
		return untyped __fiberus__("(void*)fib_atomic_ptr_compare_exchange((void**)&", this.ptr, ",(void*)(intptr_t)", expected, ",(void*)(intptr_t)", replacement, ")");
	}

	public inline function exchange(value:T):T {
		return untyped __fiberus__("(void*)fib_atomic_ptr_exchange((void**)&", this.ptr, ",(void*)(intptr_t)", value, ")");
	}

	public inline function load():T {
		return untyped __fiberus__("(void*)fib_atomic_ptr_load((void**)&", this.ptr, ")");
	}

	public inline function store(value:T):T {
		return untyped __fiberus__("(void*)fib_atomic_ptr_store((void**)&", this.ptr, ",(void*)(intptr_t)", value, ")");
	}
}

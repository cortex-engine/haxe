/*
 * Fiberus - Fiber Runtime for Haxe
 * AtomicInt.hx - Atomic integer type for lock-free concurrency
 *
 * Uses C11 atomic operations for thread-safe integer manipulation.
 */

package fiberus;

@:coreType @:notNull @:runtimeValue abstract AtomicInt from Int to Int {
	/**
	 * Atomically load the current value (acquire semantics).
	 */
	public inline function load():Int {
		return untyped __fiberus__("atomic_load(&{0})", this);
	}

	/**
	 * Atomically store a new value (release semantics).
	 */
	public inline function store(value:Int):Void {
		untyped __fiberus__("atomic_store(&{0}, {1})", this, value);
	}

	/**
	 * Atomically exchange the value, returning the old value.
	 */
	public inline function exchange(value:Int):Int {
		return untyped __fiberus__("atomic_exchange(&{0}, {1})", this, value);
	}

	/**
	 * Atomically add to the value, returning the old value.
	 */
	public inline function fetchAdd(value:Int):Int {
		return untyped __fiberus__("atomic_fetch_add(&{0}, {1})", this, value);
	}

	/**
	 * Atomically subtract from the value, returning the old value.
	 */
	public inline function fetchSub(value:Int):Int {
		return untyped __fiberus__("atomic_fetch_sub(&{0}, {1})", this, value);
	}

	/**
	 * Atomically compare and exchange.
	 * If current value equals expected, sets to desired and returns true.
	 * Otherwise, returns false.
	 */
	public inline function compareExchange(expected:Int, desired:Int):Bool {
		return untyped __fiberus__("atomic_compare_exchange_strong(&{0}, &(int){{{1}}}, {2})", this, expected, desired);
	}

	/**
	 * Atomically increment the value, returning the new value.
	 */
	public inline function increment():Int {
		return fetchAdd(1) + 1;
	}

	/**
	 * Atomically decrement the value, returning the new value.
	 */
	public inline function decrement():Int {
		return fetchSub(1) - 1;
	}
}

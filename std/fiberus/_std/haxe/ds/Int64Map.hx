/*
 * Fiberus - Fiber Runtime for Haxe
 * Int64Map.hx - Native hash map with Int64 keys
 */

package haxe.ds;

@:coreApi
extern class Int64Map<T> implements haxe.Constraints.IMap<haxe.Int64, T> {
	public function new():Void;
	public function set(key:haxe.Int64, value:T):Void;
	public function get(key:haxe.Int64):Null<T>;
	public function exists(key:haxe.Int64):Bool;
	public function remove(key:haxe.Int64):Bool;
	public function keys():Iterator<haxe.Int64>;
	public function iterator():Iterator<T>;

	@:runtime public inline function keyValueIterator():KeyValueIterator<haxe.Int64, T> {
		return new haxe.iterators.MapKeyValueIterator(this);
	}

	public function copy():Int64Map<T>;
	public function toString():String;
	public function clear():Void;
	public function size():Int;
}

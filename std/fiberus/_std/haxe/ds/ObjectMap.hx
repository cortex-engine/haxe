/*
 * Fiberus - Fiber Runtime for Haxe
 * ObjectMap.hx - Native hash map with Object keys (identity-based)
 *
 * Uses object_id for stable identity hashing (survives GC relocation).
 */

package haxe.ds;

@:coreApi
extern class ObjectMap<K:{}, V> implements haxe.Constraints.IMap<K, V> {
	public function new():Void;
	public function set(key:K, value:V):Void;
	public function get(key:K):Null<V>;
	public function exists(key:K):Bool;
	public function remove(key:K):Bool;
	public function keys():Iterator<K>;
	public function iterator():Iterator<V>;

	@:runtime public inline function keyValueIterator():KeyValueIterator<K, V> {
		return new haxe.iterators.MapKeyValueIterator(this);
	}

	public function copy():ObjectMap<K, V>;
	public function toString():String;
	public function clear():Void;
	public function size():Int;
}

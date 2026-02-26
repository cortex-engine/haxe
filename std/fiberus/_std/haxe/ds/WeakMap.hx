/*
 * Fiberus - Fiber Runtime for Haxe
 * WeakMap.hx - Native hash map with weak Object keys
 *
 * Keys are weakly held: if no other references to a key exist, the GC
 * will collect it and automatically remove the entry from the map.
 * Values are strongly held as long as their key is alive.
 *
 * Uses the same Robin Hood hash table and object_id identity hashing
 * as ObjectMap, but with GC-integrated weak key semantics.
 */

package haxe.ds;

@:coreApi
extern class WeakMap<K:{}, V> implements haxe.Constraints.IMap<K, V> {
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

	public function copy():WeakMap<K, V>;
	public function toString():String;
	public function clear():Void;
	public function size():Int;
}

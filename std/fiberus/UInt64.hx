/*
 * Fiberus - Fiber Runtime for Haxe
 * UInt64.hx - Native unsigned 64-bit integer type
 */

package fiberus;

@:coreType @:notNull @:runtimeValue abstract UInt64 from Int {
	@:to public inline function toInt():Int {
		return cast this;
	}
}

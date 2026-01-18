/*
 * Fiberus - Fiber Runtime for Haxe
 * SizeT.hx - Native size_t type (platform-dependent unsigned integer)
 */

package fiberus;

@:native("size_t") @:scalar @:coreType @:notNull extern abstract SizeT from Int to Int {}

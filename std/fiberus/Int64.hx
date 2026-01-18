/*
 * Fiberus - Fiber Runtime for Haxe
 * Int64.hx - Native signed 64-bit integer type
 */

package fiberus;

@:coreType @:notNull @:runtimeValue abstract Int64 from Int to Int {
	@:to public inline function toInt():Int {
		return cast this;
	}

	@:op(A + B) static function add(a:Int64, b:Int64):Int64;
	@:op(A - B) static function sub(a:Int64, b:Int64):Int64;
	@:op(A * B) static function mul(a:Int64, b:Int64):Int64;
	@:op(A / B) static function div(a:Int64, b:Int64):Int64;
	@:op(A % B) static function mod(a:Int64, b:Int64):Int64;

	@:op(A == B) static function eq(a:Int64, b:Int64):Bool;
	@:op(A != B) static function neq(a:Int64, b:Int64):Bool;
	@:op(A < B) static function lt(a:Int64, b:Int64):Bool;
	@:op(A <= B) static function lte(a:Int64, b:Int64):Bool;
	@:op(A > B) static function gt(a:Int64, b:Int64):Bool;
	@:op(A >= B) static function gte(a:Int64, b:Int64):Bool;

	@:op(A & B) static function and(a:Int64, b:Int64):Int64;
	@:op(A | B) static function or(a:Int64, b:Int64):Int64;
	@:op(A ^ B) static function xor(a:Int64, b:Int64):Int64;
	@:op(~A) static function complement(a:Int64):Int64;

	@:op(A << B) static function shl(a:Int64, b:Int):Int64;
	@:op(A >> B) static function shr(a:Int64, b:Int):Int64;
	@:op(A >>> B) static function ushr(a:Int64, b:Int):Int64;

	@:op(-A) static function neg(a:Int64):Int64;
}

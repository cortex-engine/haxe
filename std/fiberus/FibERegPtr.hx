/*
 * Fiberus - Fiber Runtime for Haxe
 * FibERegPtr.hx - Opaque pointer to a C FibEReg struct.
 *
 * Maps directly to FibEReg* in generated C code.
 * Used internally by EReg to hold the compiled regex handle.
 */

package fiberus;

@:native("FibEReg*") @:coreType @:notNull extern abstract FibERegPtr {}

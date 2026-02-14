/*
 * Fiberus - Fiber Runtime for Haxe
 * FibStringBufPtr.hx - Opaque pointer to a C FibStringBuf struct.
 *
 * Maps directly to FibStringBuf* in generated C code.
 * Used internally by StringBuf to hold the growable buffer handle.
 */

package fiberus;

@:native("FibStringBuf*") @:coreType @:notNull extern abstract FibStringBufPtr {}

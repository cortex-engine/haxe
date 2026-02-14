/*
 * Fiberus - Fiber Runtime for Haxe
 * FibProcessPtr.hx - Opaque pointer to a C FibProcess struct.
 *
 * Maps directly to FibProcess* in generated C code.
 * Used internally by sys.io.Process to hold the process handle.
 */

package fiberus;

@:native("FibProcess*") @:coreType @:notNull extern abstract FibProcessPtr {}

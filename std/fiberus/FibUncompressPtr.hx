/*
 * Fiberus - Fiber Runtime for Haxe
 * FibUncompressPtr.hx - Opaque pointer to a C FibUncompress struct.
 *
 * Maps directly to FibUncompress* in generated C code.
 * Used internally by haxe.zip.Uncompress to hold the streaming decompressor handle.
 */

package fiberus;

@:native("FibUncompress*") @:coreType @:notNull extern abstract FibUncompressPtr {}

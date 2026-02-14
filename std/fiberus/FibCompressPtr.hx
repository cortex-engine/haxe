/*
 * Fiberus - Fiber Runtime for Haxe
 * FibCompressPtr.hx - Opaque pointer to a C FibCompress struct.
 *
 * Maps directly to FibCompress* in generated C code.
 * Used internally by haxe.zip.Compress to hold the streaming compressor handle.
 */

package fiberus;

@:native("FibCompress*") @:coreType @:notNull extern abstract FibCompressPtr {}

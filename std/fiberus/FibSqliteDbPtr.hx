/*
 * Fiberus - Fiber Runtime for Haxe
 * FibSqliteDbPtr.hx - Opaque pointer to a C FibSqliteDb struct.
 *
 * Maps directly to FibSqliteDb* in generated C code.
 * Used internally by fiberus.db.Connection to hold the database handle.
 */

package fiberus;

@:native("FibSqliteDb*") @:coreType @:notNull extern abstract FibSqliteDbPtr {}

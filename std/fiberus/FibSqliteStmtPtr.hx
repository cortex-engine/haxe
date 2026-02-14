/*
 * Fiberus - Fiber Runtime for Haxe
 * FibSqliteStmtPtr.hx - Opaque pointer to a C FibSqliteStmt struct.
 *
 * Maps directly to FibSqliteStmt* in generated C code.
 * Used internally by fiberus.db.ResultSet to hold the statement handle.
 */

package fiberus;

@:native("FibSqliteStmt*") @:coreType @:notNull extern abstract FibSqliteStmtPtr {}

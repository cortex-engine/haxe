/*
 * Fiberus - Fiber Runtime for Haxe
 * fiberus.db.ResultSet - Prepared statement + result iteration
 *
 * Wraps FibSqliteStmt* (sqlite_fib.h). Supports:
 * - Parameter binding (by index, 1-based)
 * - Row iteration via step()
 * - Column value access (by index, 0-based)
 * - Reset for re-execution with new bindings
 *
 * Column type constants match SQLite:
 *   1=INTEGER, 2=FLOAT, 3=TEXT, 4=BLOB, 5=NULL
 */

package fiberus.db;

import fiberus.FibSqliteDbPtr;
import fiberus.FibSqliteStmtPtr;

class ResultSet {
	var stmt:FibSqliteStmtPtr;

	/* SQLite column type constants */
	public static inline var SQLITE_INTEGER:Int = 1;
	public static inline var SQLITE_FLOAT:Int = 2;
	public static inline var SQLITE_TEXT:Int = 3;
	public static inline var SQLITE_BLOB:Int = 4;
	public static inline var SQLITE_NULL:Int = 5;

	/**
	 * Prepare a SQL statement on the given database connection.
	 * Throws on error.
	 */
	public function new(db:FibSqliteDbPtr, sql:String) {
		stmt = untyped __fiberus__("fib_sqlite_prepare(", db, ", ", sql, ")");
		var isNull:Bool = untyped __fiberus__("(", stmt, " == NULL)");
		if (isNull) {
			var errmsg:String = untyped __fiberus__("(FibString*)fib_sqlite_errmsg(", db, ")");
			throw "SQLite prepare error: " + (errmsg != null ? errmsg : "unknown");
		}
	}

	/* ====================================================================
	 * Parameter Binding (1-indexed)
	 * ==================================================================== */

	/**
	 * Bind an integer value to parameter at index (1-based).
	 */
	public function bindInt(idx:Int, value:Int):Void {
		var rc:Int = untyped __fiberus__("fib_sqlite_bind_int(", stmt, ", ", idx, ", ", value, ")");
		if (rc != 0)
			throw "SQLite bind_int failed";
	}

	/**
	 * Bind a 64-bit integer value to parameter at index (1-based).
	 */
	public function bindInt64(idx:Int, value:haxe.Int64):Void {
		var rc:Int = untyped __fiberus__("fib_sqlite_bind_int64(", stmt, ", ", idx, ", ", value, ")");
		if (rc != 0)
			throw "SQLite bind_int64 failed";
	}

	/**
	 * Bind a float value to parameter at index (1-based).
	 */
	public function bindFloat(idx:Int, value:Float):Void {
		var rc:Int = untyped __fiberus__("fib_sqlite_bind_double(", stmt, ", ", idx, ", ", value, ")");
		if (rc != 0)
			throw "SQLite bind_double failed";
	}

	/**
	 * Bind a string value to parameter at index (1-based).
	 * Passing null binds SQL NULL.
	 */
	public function bindText(idx:Int, value:String):Void {
		var rc:Int = untyped __fiberus__("fib_sqlite_bind_text(", stmt, ", ", idx, ", ", value, ")");
		if (rc != 0)
			throw "SQLite bind_text failed";
	}

	/**
	 * Bind a blob value to parameter at index (1-based).
	 */
	public function bindBlob(idx:Int, data:haxe.io.Bytes):Void {
		var bd = data.getData();
		var len = data.length;
		var rc:Int = untyped __fiberus__("fib_sqlite_bind_blob(", stmt, ", ", idx, ", ", bd, ", ", len, ")");
		if (rc != 0)
			throw "SQLite bind_blob failed";
	}

	/**
	 * Bind NULL to parameter at index (1-based).
	 */
	public function bindNull(idx:Int):Void {
		var rc:Int = untyped __fiberus__("fib_sqlite_bind_null(", stmt, ", ", idx, ")");
		if (rc != 0)
			throw "SQLite bind_null failed";
	}

	/**
	 * Get the number of bind parameters in the statement.
	 */
	public function parameterCount():Int {
		return untyped __fiberus__("fib_sqlite_bind_parameter_count(", stmt, ")");
	}

	/**
	 * Get the name of a bind parameter (1-indexed). Returns null if unnamed.
	 */
	public function parameterName(idx:Int):String {
		return untyped __fiberus__("(FibString*)fib_sqlite_bind_parameter_name(", stmt, ", ", idx, ")");
	}

	/**
	 * Get the index of a named bind parameter. Returns 0 if not found.
	 */
	public function parameterIndex(name:String):Int {
		return untyped __fiberus__("fib_sqlite_bind_parameter_index(", stmt, ", ", name, ")");
	}

	/* ====================================================================
	 * Row Iteration
	 * ==================================================================== */

	/**
	 * Step the statement. Returns true if a row is available, false if done.
	 * Throws on error.
	 */
	public function step():Bool {
		var rc:Int = untyped __fiberus__("fib_sqlite_step(", stmt, ")");
		if (rc == 1)
			return true;
		if (rc == 0)
			return false;
		throw "SQLite step error";
	}

	/**
	 * Reset the statement for re-execution (e.g. with new bindings).
	 */
	public function reset():Void {
		var rc:Int = untyped __fiberus__("fib_sqlite_reset(", stmt, ")");
		if (rc != 0)
			throw "SQLite reset error";
	}

	/**
	 * Finalize and release the statement. Must not be used after this.
	 */
	public function close():Void {
		untyped __fiberus__("fib_sqlite_finalize(", stmt, ")");
	}

	/* ====================================================================
	 * Column Accessors (0-indexed, valid after step() returns true)
	 * ==================================================================== */

	/**
	 * Get the number of columns in the result set.
	 */
	public function columnCount():Int {
		return untyped __fiberus__("fib_sqlite_column_count(", stmt, ")");
	}

	/**
	 * Get the name of a column (0-indexed).
	 */
	public function columnName(col:Int):String {
		return untyped __fiberus__("(FibString*)fib_sqlite_column_name(", stmt, ", ", col, ")");
	}

	/**
	 * Get the SQLite type of a column value.
	 * Returns one of: SQLITE_INTEGER(1), SQLITE_FLOAT(2), SQLITE_TEXT(3),
	 *                  SQLITE_BLOB(4), SQLITE_NULL(5)
	 */
	public function columnType(col:Int):Int {
		return untyped __fiberus__("fib_sqlite_column_type(", stmt, ", ", col, ")");
	}

	/**
	 * Get an integer column value (0-indexed).
	 */
	public function columnInt(col:Int):Int {
		return untyped __fiberus__("fib_sqlite_column_int(", stmt, ", ", col, ")");
	}

	/**
	 * Get a 64-bit integer column value (0-indexed).
	 */
	public function columnInt64(col:Int):haxe.Int64 {
		return untyped __fiberus__("fib_sqlite_column_int64(", stmt, ", ", col, ")");
	}

	/**
	 * Get a float column value (0-indexed).
	 */
	public function columnFloat(col:Int):Float {
		return untyped __fiberus__("fib_sqlite_column_double(", stmt, ", ", col, ")");
	}

	/**
	 * Get a text column value (0-indexed). Returns null for SQL NULL.
	 */
	public function columnText(col:Int):String {
		return untyped __fiberus__("(FibString*)fib_sqlite_column_text(", stmt, ", ", col, ")");
	}

	/**
	 * Get the byte size of a column value (0-indexed).
	 * Useful for BLOB columns.
	 */
	public function columnBytes(col:Int):Int {
		return untyped __fiberus__("fib_sqlite_column_bytes(", stmt, ", ", col, ")");
	}

	/**
	 * Get a BLOB column value as Bytes (0-indexed). Returns null for SQL NULL.
	 */
	public function columnBlob(col:Int):haxe.io.Bytes {
		var bd:haxe.io.BytesData = untyped __fiberus__("(FibBytesData*)fib_sqlite_column_blob(", stmt, ", ", col, ", NULL)");
		var isNull:Bool = untyped __fiberus__("(", bd, " == NULL)");
		if (isNull)
			return null;
		return haxe.io.Bytes.ofData(bd);
	}
}

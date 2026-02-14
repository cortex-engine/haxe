/*
 * Fiberus - Fiber Runtime for Haxe
 * fiberus.db.Connection - SQLite database connection
 *
 * Wraps FibSqliteDb* (sqlite_fib.h) to provide a clean Haxe API.
 * Supports exec (DDL/DML), prepare (parameterized queries), and
 * metadata (lastInsertRowId, changes, errorMessage).
 */

package fiberus.db;

import fiberus.FibSqliteDbPtr;

class Connection {
	var db:FibSqliteDbPtr;

	/**
	 * Open a SQLite database connection.
	 * Use ":memory:" for an in-memory database.
	 * Throws on failure.
	 */
	public function new(path:String) {
		db = untyped __fiberus__("fib_sqlite_open(", path, ")");
		var isNull:Bool = untyped __fiberus__("(", db, " == NULL)");
		if (isNull)
			throw "Failed to open SQLite database: " + path;
	}

	/**
	 * Execute one or more SQL statements that don't return rows.
	 * Throws on error.
	 */
	public function exec(sql:String):Void {
		var rc:Int = untyped __fiberus__("fib_sqlite_exec(", db, ", ", sql, ")");
		if (rc != 0)
			throw "SQLite exec error: " + errorMessage();
	}

	/**
	 * Prepare a SQL statement for execution with parameters.
	 * Returns a ResultSet which can be used to bind parameters and iterate rows.
	 * Throws on error.
	 */
	public function prepare(sql:String):ResultSet {
		return new ResultSet(db, sql);
	}

	/**
	 * Get the rowid of the last inserted row.
	 */
	public function lastInsertRowId():haxe.Int64 {
		return untyped __fiberus__("fib_sqlite_last_insert_rowid(", db, ")");
	}

	/**
	 * Get the number of rows changed by the last INSERT/UPDATE/DELETE.
	 */
	public function changes():Int {
		return untyped __fiberus__("fib_sqlite_changes(", db, ")");
	}

	/**
	 * Get the last error message, or null if none.
	 */
	public function errorMessage():String {
		return untyped __fiberus__("(FibString*)fib_sqlite_errmsg(", db, ")");
	}

	/**
	 * Close the database connection. The connection must not be used after this.
	 */
	public function close():Void {
		untyped __fiberus__("fib_sqlite_close(", db, ")");
	}
}

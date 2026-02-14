/*
 * Fiberus - Fiber Runtime for Haxe
 * fiberus.db.Sqlite - SQLite3 database factory
 *
 * Provides static methods to open SQLite database connections.
 * Uses the vendored sqlite-3.40.1 amalgamation compiled with
 * SQLITE_THREADSAFE=0 (single-threaded, appropriate for fiber-per-connection).
 *
 * Usage:
 *   var db = Sqlite.open("mydb.sqlite");
 *   db.exec("CREATE TABLE t (id INTEGER PRIMARY KEY, name TEXT)");
 *   var rs = db.prepare("SELECT * FROM t");
 *   while (rs.step()) {
 *       trace(rs.columnText(0));
 *   }
 *   rs.close();
 *   db.close();
 */

package fiberus.db;

class Sqlite {
	/**
	 * Open a SQLite database file.
	 * Use ":memory:" for an in-memory database.
	 * Throws on failure.
	 */
	public static function open(path:String):Connection {
		return new Connection(path);
	}
}

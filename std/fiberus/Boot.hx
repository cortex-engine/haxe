/*
 * Fiberus Boot - Runtime initialization
 */
package fiberus;

@:keep
class Boot {
	public static function __string_rec(o:Dynamic, s:String):String {
		if (o == null)
			return "null";
		// Handle primitive types directly to avoid infinite recursion
		// Std.string -> __string_rec -> Std.string loop
		if (untyped __fiberus__("(", o, ").type == FIB_TYPE_BOOL"))
			return untyped __fiberus__("fib_string_new((", o, ").data.boolVal ? \"true\" : \"false\")");
		if (untyped __fiberus__("(", o, ").type == FIB_TYPE_INT"))
			return untyped __fiberus__("fib_string_from_int((", o, ").data.intVal)");
		if (untyped __fiberus__("(", o, ").type == FIB_TYPE_FLOAT"))
			return untyped __fiberus__("fib_string_from_float((", o, ").data.floatVal)");
		if (untyped __fiberus__("(", o, ").type == FIB_TYPE_STRING"))
			return untyped __fiberus__("(", o, ").data.stringVal");
		if (untyped __fiberus__("(", o, ").type == FIB_TYPE_ARRAY"))
			return "[Array]";
		if (untyped __fiberus__("(", o, ").type == FIB_TYPE_OBJECT"))
			return "[Object]";
		return "[Unknown]";
	}

	public static function __instanceof(v:Dynamic, t:Dynamic):Bool {
		// TODO: Implement proper type checking
		return false;
	}
}

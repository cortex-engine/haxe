/*
 * Copyright (C)2005-2019 Haxe Foundation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

@:coreApi
class Reflect {
	public static function hasField(o:Dynamic, field:String):Bool {
		if (o == null || field == null)
			return false;
		return untyped __fiberus__("fib_reflect_has_field(", o, ", fib_string_data(", field, "))");
	}

	public static function field(o:Dynamic, field:String):Dynamic {
		if (o == null || field == null)
			return null;
		return untyped __fiberus__("fib_reflect_field(", o, ", fib_string_data(", field, "))");
	}

	public static function setField(o:Dynamic, field:String, value:Dynamic):Void {
		if (o == null || field == null)
			return;
		untyped __fiberus__("fib_reflect_set_field(&", o, ", fib_string_data(", field, "), ", value, ")");
	}

	public static function getProperty(o:Dynamic, field:String):Dynamic {
		// Fiberus doesn't have property accessor dispatch at runtime,
		// so this behaves the same as field()
		if (o == null || field == null)
			return null;
		return untyped __fiberus__("fib_reflect_field(", o, ", fib_string_data(", field, "))");
	}

	public static function setProperty(o:Dynamic, field:String, value:Dynamic):Void {
		// Same as setField since we don't have runtime property dispatch
		if (o == null || field == null)
			return;
		untyped __fiberus__("fib_reflect_set_field(&", o, ", fib_string_data(", field, "), ", value, ")");
	}

	public static function callMethod(o:Dynamic, func:haxe.Constraints.Function, args:Array<Dynamic>):Dynamic {
		if (func == null)
			return null;
		var closure:Dynamic = func;
		var argArr:Dynamic = args;
		var argCount:Int = (args != null) ? args.length : 0;
		return untyped __fiberus__("fib_closure_call_dynamic((FibClosure*)fib_dynamic_to_object(", closure, "), ", argArr, " ? ", argArr, "->data.arrayVal->data : NULL, ", argCount, ")");
	}

	public static function fields(o:Dynamic):Array<String> {
		if (o == null)
			return [];
		var arr:Dynamic = untyped __fiberus__("fib_dynamic_array(fib_reflect_fields(", o, "))");
		return arr;
	}

	public static function isFunction(f:Dynamic):Bool {
		if (f == null)
			return false;
		return untyped __fiberus__("fib_reflect_is_function(", f, ")");
	}

	public static function compare<T>(a:T, b:T):Int {
		var da:Dynamic = a;
		var db:Dynamic = b;
		return untyped __fiberus__("fib_reflect_compare(", da, ", ", db, ")");
	}

	public static function compareMethods(f1:Dynamic, f2:Dynamic):Bool {
		if (f1 == null || f2 == null)
			return false;
		return untyped __fiberus__("fib_reflect_compare_methods(", f1, ", ", f2, ")");
	}

	public static function isObject(v:Dynamic):Bool {
		if (v == null)
			return false;
		return untyped __fiberus__("fib_reflect_is_object(", v, ")");
	}

	public static function isEnumValue(v:Dynamic):Bool {
		if (v == null)
			return false;
		return untyped __fiberus__("fib_reflect_is_enum_value(", v, ")");
	}

	public static function deleteField(o:Dynamic, field:String):Bool {
		if (o == null || field == null)
			return false;
		return untyped __fiberus__("fib_anon_delete_field(&", o, ", fib_string_data(", field, "))");
	}

	public static function copy<T>(o:Null<T>):Null<T> {
		if (o == null)
			return null;
		var d:Dynamic = o;
		return untyped __fiberus__("fib_reflect_copy(", d, ")");
	}

	public static function makeVarArgs<T>(f:Array<Dynamic>->T):Dynamic {
		// Fiberus doesn't support varargs transformation yet.
		// Return the function as-is wrapped in a closure.
		return cast f;
	}
}

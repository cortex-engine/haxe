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

enum ValueType {
	TNull;
	TInt;
	TInt64;
	TFloat;
	TBool;
	TObject;
	TFunction;
	TClass(c:Class<Dynamic>);
	TEnum(e:Enum<Dynamic>);
	TUnknown;
}

@:coreApi class Type {
	public static function getClass<T>(o:T):Null<Class<T>> {
		if (o == null)
			return null;
		var d:Dynamic = o;
		// String -> String_class
		if (untyped __fiberus__("(", d, ").type == FIB_TYPE_STRING"))
			return untyped __fiberus__("(FibDynamic){ .type = FIB_TYPE_CLASS, .data.ptrVal = &String_class }");
		// Array -> Array_class (sentinel, matches TTypeExpr Array)
		if (untyped __fiberus__("(", d, ").type == FIB_TYPE_ARRAY"))
			return untyped __fiberus__("(FibDynamic){ .type = FIB_TYPE_CLASS, .data.ptrVal = &Array_class }");
		// Only class instances (FIB_TYPE_OBJECT) have classes, excluding closures
		if (untyped __fiberus__("(", d, ").type != FIB_TYPE_OBJECT"))
			return null;
		if (untyped __fiberus__("(", d, ").data.objectVal == NULL"))
			return null;
		var clazz:Dynamic = untyped __fiberus__("(FibDynamic){ .type = FIB_TYPE_CLASS, .data.ptrVal = (", d, ").data.objectVal->clazz }");
		// Exclude closures
		if (untyped __fiberus__("((FibClass*)(", clazz, ").data.ptrVal)->classId == FIB_CLASS_ID_CLOSURE"))
			return null;
		return clazz;
	}

	public static function getEnum(o:EnumValue):Null<Enum<Dynamic>> {
		if (o == null)
			return null;
		var d:Dynamic = o;
		if (untyped __fiberus__("(", d, ").type != FIB_TYPE_ENUM"))
			return null;
		if (untyped __fiberus__("fib_enum_meta(", d, ") == NULL"))
			return null;
		var meta:Dynamic = untyped __fiberus__("(FibDynamic){ .type = FIB_TYPE_CLASS, .data.ptrVal = (void*)fib_enum_meta(", d, ") }");
		return meta;
	}

	public static function getSuperClass(c:Class<Dynamic>):Null<Class<Dynamic>> {
		if (c == null)
			return null;
		var d:Dynamic = c;
		var sup:Dynamic = untyped __fiberus__("((FibClass*)(", d, ").data.ptrVal)->super ? (FibDynamic){ .type = FIB_TYPE_CLASS, .data.ptrVal = ((FibClass*)(", d, ").data.ptrVal)->super } : fib_dynamic_null()");
		if (sup == null)
			return null;
		return sup;
	}

	public static function getClassName(c:Class<Dynamic>):String {
		if (c == null)
			return null;
		var d:Dynamic = c;
		return untyped __fiberus__("fib_string_new(((FibClass*)(", d, ").data.ptrVal)->name)");
	}

	public static function getEnumName(e:Enum<Dynamic>):String {
		if (e == null)
			return null;
		var d:Dynamic = e;
		if (untyped __fiberus__("(", d, ").data.ptrVal == NULL"))
			return null;
		return untyped __fiberus__("fib_string_new(((FibEnumMeta*)(", d, ").data.ptrVal)->name)");
	}

	public static function resolveClass(name:String):Null<Class<Dynamic>> {
		if (name == null)
			return null;
		var result:Dynamic = untyped __fiberus__("fib_class_by_name(fib_string_data(", name, ")) ? (FibDynamic){ .type = FIB_TYPE_CLASS, .data.ptrVal = fib_class_by_name(fib_string_data(", name, ")) } : fib_dynamic_null()");
		if (result == null)
			return null;
		return result;
	}

	public static function resolveEnum(name:String):Null<Enum<Dynamic>> {
		if (name == null)
			return null;
		var result:Dynamic = untyped __fiberus__("fib_enum_by_name(fib_string_data(", name, ")) ? (FibDynamic){ .type = FIB_TYPE_CLASS, .data.ptrVal = (void*)fib_enum_by_name(fib_string_data(", name, ")) } : fib_dynamic_null()");
		if (result == null)
			return null;
		return result;
	}

	public static function createInstance<T>(cl:Class<T>, args:Array<Dynamic>):T {
		if (cl == null)
			return null;
		var d:Dynamic = cl;
		// Special case: String_class — just return the first argument as string
		if (untyped __fiberus__("(FibClass*)(", d, ").data.ptrVal == &String_class")) {
			if (args != null && args.length > 0)
				return args[0];
			return untyped __fiberus__("fib_dynamic_string(fib_string_new(\"\"))");
		}
		var a:Dynamic = args;
		return untyped __fiberus__("(FibDynamic){ .type = FIB_TYPE_OBJECT, .data.ptrVal = fib_create_instance((FibClass*)(", d,
			").data.ptrVal, ((FibArray*)(", a, ").data.ptrVal)->data, ((FibArray*)(", a, ").data.ptrVal)->length) }");
	}

	public static function createEmptyInstance<T>(cl:Class<T>):T {
		if (cl == null)
			return null;
		var d:Dynamic = cl;
		return untyped __fiberus__("(FibDynamic){ .type = FIB_TYPE_OBJECT, .data.ptrVal = fib_create_empty_instance((FibClass*)(", d, ").data.ptrVal) }");
	}

	public static function createEnum<T>(e:Enum<T>, constr:String, ?params:Array<Dynamic>):T {
		if (e == null || constr == null)
			return null;
		var d:Dynamic = e;
		// Find constructor by name
		var count:Int = untyped __fiberus__("((FibEnumMeta*)(", d, ").data.ptrVal)->constr_count");
		var i = 0;
		while (i < count) {
			var cname:String = untyped __fiberus__("fib_string_new(((FibEnumMeta*)(", d, ").data.ptrVal)->constrs[", i, "].name)");
			if (cname == constr) {
				var expectedParams:Int = untyped __fiberus__("((FibEnumMeta*)(", d, ").data.ptrVal)->constrs[", i, "].param_count");
				var actualParams:Int = (params != null) ? params.length : 0;
				if (expectedParams != actualParams)
					throw "Invalid enum constructor parameters for " + constr;
				if (actualParams > 0) {
					var a:Dynamic = params;
					return untyped __fiberus__("fib_enum_create((FibEnumMeta*)(", d, ").data.ptrVal, ", i,
						", ((FibArray*)(", a, ").data.ptrVal)->data, ((FibArray*)(", a, ").data.ptrVal)->length)");
				} else {
					return untyped __fiberus__("fib_enum_create((FibEnumMeta*)(", d, ").data.ptrVal, ", i, ", NULL, 0)");
				}
			}
			i++;
		}
		throw "Unknown enum constructor " + constr;
	}

	public static function createEnumIndex<T>(e:Enum<T>, index:Int, ?params:Array<Dynamic>):T {
		if (e == null)
			return null;
		var d:Dynamic = e;
		if (params != null && params.length > 0) {
			var a:Dynamic = params;
			return untyped __fiberus__("fib_enum_create((FibEnumMeta*)(", d, ").data.ptrVal, ", index,
				", ((FibArray*)(", a, ").data.ptrVal)->data, ((FibArray*)(", a, ").data.ptrVal)->length)");
		} else {
			return untyped __fiberus__("fib_enum_create((FibEnumMeta*)(", d, ").data.ptrVal, ", index, ", NULL, 0)");
		}
	}

	public static function getInstanceFields(c:Class<Dynamic>):Array<String> {
		if (c == null)
			return [];
		var d:Dynamic = c;
		var arr:Dynamic = untyped __fiberus__("fib_dynamic_array(fib_class_get_instance_fields((FibClass*)(", d, ").data.ptrVal))");
		return arr;
	}

	public static function getClassFields(c:Class<Dynamic>):Array<String> {
		if (c == null)
			return [];
		var d:Dynamic = c;
		var arr:Dynamic = untyped __fiberus__("fib_dynamic_array(fib_class_get_class_fields((FibClass*)(", d, ").data.ptrVal))");
		return arr;
	}

	public static function getEnumConstructs(e:Enum<Dynamic>):Array<String> {
		if (e == null)
			return [];
		var d:Dynamic = e;
		var count:Int = untyped __fiberus__("((FibEnumMeta*)(", d, ").data.ptrVal)->constr_count");
		var result:Array<String> = [];
		var i = 0;
		while (i < count) {
			var name:String = untyped __fiberus__("fib_string_new(((FibEnumMeta*)(", d, ").data.ptrVal)->constrs[", i, "].name)");
			result.push(name);
			i++;
		}
		return result;
	}

	public static function typeof(v:Dynamic):ValueType {
		if (v == null)
			return TNull;
		if (untyped __fiberus__("(", v, ").type == FIB_TYPE_BOOL"))
			return TBool;
		if (untyped __fiberus__("(", v, ").type == FIB_TYPE_INT64"))
			return TInt64;
		if (untyped __fiberus__("(", v, ").type == FIB_TYPE_INT"))
			return TInt;
		if (untyped __fiberus__("(", v, ").type == FIB_TYPE_FLOAT")) {
			// Haxe convention: a float with no fractional part that fits in Int32 is TInt
			if (untyped __fiberus__("(", v, ").data.floatVal == (double)(int32_t)(", v, ").data.floatVal"))
				return TInt;
			return TFloat;
		}
		if (untyped __fiberus__("(", v, ").type == FIB_TYPE_STRING")) {
			var stringClass:Dynamic = untyped __fiberus__("(FibDynamic){ .type = FIB_TYPE_CLASS, .data = { .ptrVal = &String_class } }");
			return TClass(stringClass);
		}
		if (untyped __fiberus__("(", v, ").type == FIB_TYPE_ENUM"))
			return TEnum(getEnum(cast v));
		if (untyped __fiberus__("(", v, ").type == FIB_TYPE_OBJECT")) {
			// Check if it's a closure
			if (untyped __fiberus__("(", v, ").data.objectVal != NULL && (", v, ").data.objectVal->clazz != NULL && (", v, ").data.objectVal->clazz->classId == FIB_CLASS_ID_CLOSURE"))
				return TFunction;
			return TClass(getClass(v));
		}
		if (untyped __fiberus__("(", v, ").type == FIB_TYPE_ANON"))
			return TObject;
		if (untyped __fiberus__("(", v, ").type == FIB_TYPE_ARRAY")) {
			var arrayClass:Dynamic = untyped __fiberus__("(FibDynamic){ .type = FIB_TYPE_CLASS, .data = { .ptrVal = &Array_class } }");
			return TClass(arrayClass);
		}
		if (untyped __fiberus__("(", v, ").type == FIB_TYPE_CLASS"))
			return TObject;
		return TUnknown;
	}

	public static function enumEq<T:EnumValue>(a:T, b:T):Bool {
		if (a == null && b == null)
			return true;
		if (a == null || b == null)
			return false;
		var da:Dynamic = a;
		var db:Dynamic = b;
		return untyped __fiberus__("fib_enum_eq(", da, ", ", db, ")");
	}

	public static function enumConstructor(e:EnumValue):String {
		if (e == null)
			return null;
		var d:Dynamic = e;
		return untyped __fiberus__("fib_string_new(fib_enum_tag(", d, "))");
	}

	public static function enumParameters(e:EnumValue):Array<Dynamic> {
		if (e == null)
			return [];
		var d:Dynamic = e;
		var count:Int = untyped __fiberus__("fib_enum_param_count(", d, ")");
		var result:Array<Dynamic> = [];
		var i = 0;
		while (i < count) {
			var param:Dynamic = untyped __fiberus__("fib_enum_param(", d, ", ", i, ")");
			result.push(param);
			i++;
		}
		return result;
	}

	public static function enumIndex(e:EnumValue):Int {
		if (e == null)
			return -1;
		var d:Dynamic = e;
		return untyped __fiberus__("fib_enum_index(", d, ")");
	}

	public static function allEnums<T>(e:Enum<T>):Array<T> {
		if (e == null)
			return [];
		var d:Dynamic = e;
		var count:Int = untyped __fiberus__("((FibEnumMeta*)(", d, ").data.ptrVal)->constr_count");
		var result:Array<T> = [];
		var i = 0;
		while (i < count) {
			var paramCount:Int = untyped __fiberus__("((FibEnumMeta*)(", d, ").data.ptrVal)->constrs[", i, "].param_count");
			if (paramCount == 0) {
				// No-param constructor: create it with no params
				var val:T = untyped __fiberus__("fib_enum_create((FibEnumMeta*)(", d, ").data.ptrVal, ", i, ", NULL, 0)");
				result.push(val);
			}
			i++;
		}
		return result;
	}
}

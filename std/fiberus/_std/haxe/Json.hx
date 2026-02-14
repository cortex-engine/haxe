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

package haxe;

/**
	Fiberus JSON implementation using simdjson for parsing and a custom
	C stringify implementation. Falls back to pure-Haxe JsonPrinter for
	stringify with replacer support.

	@see https://haxe.org/manual/std-Json.html
**/
class Json {
	/**
		Parses given JSON-encoded `text` and returns the resulting object.

		JSON objects are parsed into anonymous structures and JSON arrays
		are parsed into `Array<Dynamic>`.

		If given `text` is not valid JSON, an exception will be thrown.
	**/
	public static function parse(text:String):Dynamic {
		var error:String = null;
		var result:Dynamic = untyped __fiberus__("fib_json_parse(", text, ", (FibString**)&", error, ")");
		if (error != null) {
			throw error;
		}
		return result;
	}

	/**
		Encodes the given `value` and returns the resulting JSON string.

		If `replacer` is given and is not null, it is used to retrieve the
		actual object to be encoded. The `replacer` function takes two parameters,
		the key and the value being encoded. Initial key value is an empty string.

		If `space` is given and is not null, the result will be pretty-printed.
		Successive levels will be indented by this string.
	**/
	public static function stringify(value:Dynamic, ?replacer:(key:Dynamic, value:Dynamic) -> Dynamic, ?space:String):String {
		if (replacer != null) {
			return haxe.format.JsonPrinter.print(value, replacer, space);
		}
		/* Fast path: native C stringify */
		return untyped __fiberus__("fib_json_stringify(", value, ", ", space, ")");
	}
}

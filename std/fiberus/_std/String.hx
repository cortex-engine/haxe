/*
 * Fiberus String implementation
 * 
 * Haxe strings are immutable and implemented as FibString* in C.
 * Most string operations are delegated to the fib_string_* functions.
 */

@:coreApi
@:nativeType("FibString*")
extern class String {
    var length(default, null):Int;

    function new(string:String):Void;
    function toUpperCase():String;
    function toLowerCase():String;
    function charAt(index:Int):String;
    function charCodeAt(index:Int):Null<Int>;
    function split(delimiter:String):Array<String>;
    function substr(pos:Int, ?len:Int):String;
    function substring(startIndex:Int, ?endIndex:Int):String;
    function toString():String;

    /**
     * Find first occurrence of str in this string.
     * Returns -1 if not found.
     */
    function indexOf(str:String, ?startIndex:Int):Int;

    /**
     * Find last occurrence of str in this string.
     * Returns -1 if not found.
     */
    function lastIndexOf(str:String, ?startIndex:Int):Int;

    static function fromCharCode(code:Int):String;
}

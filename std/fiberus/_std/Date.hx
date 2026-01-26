/*
 * Fiberus Date implementation
 * 
 * Provides date/time functionality using C time functions.
 * The internal representation stores the timestamp in seconds since epoch.
 */

@:coreApi
class Date {
    private var mSeconds:Float;

    public function new(year:Int, month:Int, day:Int, hour:Int, min:Int, sec:Int):Void {
        mSeconds = untyped __fiberus__("fib_date_new(", year, ",", month, ",", day, ",", hour, ",", min, ",", sec, ")");
    }

    public function getTime():Float {
        return mSeconds * 1000.0;
    }

    public function getHours():Int {
        return untyped __fiberus__("fib_date_get_hours(", mSeconds, ")");
    }

    public function getMinutes():Int {
        return untyped __fiberus__("fib_date_get_minutes(", mSeconds, ")");
    }

    public function getSeconds():Int {
        return untyped __fiberus__("fib_date_get_seconds(", mSeconds, ")");
    }

    public function getFullYear():Int {
        return untyped __fiberus__("fib_date_get_year(", mSeconds, ")");
    }

    public function getMonth():Int {
        return untyped __fiberus__("fib_date_get_month(", mSeconds, ")");
    }

    public function getDate():Int {
        return untyped __fiberus__("fib_date_get_date(", mSeconds, ")");
    }

    public function getDay():Int {
        return untyped __fiberus__("fib_date_get_day(", mSeconds, ")");
    }

    public function getUTCHours():Int {
        return untyped __fiberus__("fib_date_get_utc_hours(", mSeconds, ")");
    }

    public function getUTCMinutes():Int {
        return untyped __fiberus__("fib_date_get_utc_minutes(", mSeconds, ")");
    }

    public function getUTCSeconds():Int {
        return untyped __fiberus__("fib_date_get_utc_seconds(", mSeconds, ")");
    }

    public function getUTCFullYear():Int {
        return untyped __fiberus__("fib_date_get_utc_year(", mSeconds, ")");
    }

    public function getUTCMonth():Int {
        return untyped __fiberus__("fib_date_get_utc_month(", mSeconds, ")");
    }

    public function getUTCDate():Int {
        return untyped __fiberus__("fib_date_get_utc_date(", mSeconds, ")");
    }

    public function getUTCDay():Int {
        return untyped __fiberus__("fib_date_get_utc_day(", mSeconds, ")");
    }

    public function getTimezoneOffset():Int {
        return untyped __fiberus__("fib_date_get_timezone_offset(", mSeconds, ")");
    }

    public function toString():String {
        return untyped __fiberus__("fib_date_to_string(", mSeconds, ")");
    }

    public static function now():Date {
        var result = new Date(0, 0, 0, 0, 0, 0);
        result.mSeconds = untyped __fiberus__("fib_date_now()");
        return result;
    }

    public static function fromTime(t:Float):Date {
        var result = new Date(0, 0, 0, 0, 0, 0);
        result.mSeconds = t * 0.001;
        return result;
    }

    public static function fromString(s:String):Date {
        switch (s.length) {
            case 8: // hh:mm:ss
                var k = s.split(":");
                return Date.fromTime(Std.parseInt(k[0]) * 3600000. + Std.parseInt(k[1]) * 60000. + Std.parseInt(k[2]) * 1000.);
            case 10: // YYYY-MM-DD
                var k = s.split("-");
                return new Date(Std.parseInt(k[0]), Std.parseInt(k[1]) - 1, Std.parseInt(k[2]), 0, 0, 0);
            case 19: // YYYY-MM-DD hh:mm:ss
                var k = s.split(" ");
                var y = k[0].split("-");
                var t = k[1].split(":");
                return new Date(Std.parseInt(y[0]), Std.parseInt(y[1]) - 1, Std.parseInt(y[2]), Std.parseInt(t[0]), Std.parseInt(t[1]), Std.parseInt(t[2]));
            default:
                throw "Invalid date format : " + s;
        }
    }
}

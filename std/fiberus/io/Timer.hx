package fiberus.io;

/**
 * Timer operations using io_uring timeouts.
 * Suspends the calling fiber without blocking the OS thread.
 * 
 * This is the foundation for Sys.sleep() in Fiberus.
 */
class Timer {
    /**
     * Sleep for the specified number of milliseconds.
     * Suspends the fiber, allowing other fibers to run.
     */
    public static function sleep(milliseconds:Int):Void {
        untyped __fiberus__("fib_io_sleep_ms(", milliseconds, ")");
    }
    
    /**
     * Sleep for the specified number of microseconds.
     */
    public static function sleepMicros(microseconds:Int):Void {
        untyped __fiberus__("fib_io_sleep_ns((uint64_t)", microseconds, " * 1000ULL)");
    }
    
    /**
     * Sleep for the specified number of nanoseconds.
     */
    public static function sleepNanos(nanoseconds:haxe.Int64):Void {
        untyped __fiberus__("fib_io_sleep_ns((uint64_t)", nanoseconds, ")");
    }
    
    /**
     * Sleep for the specified number of seconds (floating point).
     * This is the primary interface matching Sys.sleep().
     */
    public static function sleepSeconds(seconds:Float):Void {
        untyped __fiberus__("fib_io_sleep(", seconds, ")");
    }
}

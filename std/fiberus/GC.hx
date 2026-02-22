/*
 * Fiberus GC - Garbage collection API
 */
package fiberus;

/**
 * GC statistics structure.
 * Contains information about the garbage collector's state and performance.
 */
typedef GCStats = {
	/** Total number of gc_alloc() calls since startup */
	var totalAllocations:Int;
	/** Total bytes allocated since startup */
	var totalBytesAllocated:Int;
	/** Current live heap size in bytes */
	var currentHeapSize:Int;
	/** Peak heap size reached */
	var peakHeapSize:Int;
	/** Current number of live objects */
	var currentObjectCount:Int;
	/** Total number of GC cycles (major collections) */
	var collectionCount:Int;
	/** Objects marked in last cycle */
	var objectsMarked:Int;
	/** Objects freed in last cycle */
	var objectsSwept:Int;
	/** Bytes freed in last cycle */
	var bytesFreed:Int;
	/** Last mark phase time in milliseconds */
	var lastMarkTimeMs:Float;
	/** Last sweep phase time in milliseconds */
	var lastSweepTimeMs:Float;
	/** Total time spent in GC in milliseconds */
	var totalGcTimeMs:Float;
	/** Fiber stacks scanned in last cycle */
	var fibersScanned:Int;
	/** Total stack bytes scanned in last cycle */
	var stackBytesScanned:Int;
	
	/* Generational GC stats */
	/** Total minor (nursery) collections */
	var minorCollections:Int;
	/** Objects promoted from nursery to mature space */
	var minorObjectsEvacuated:Int;
	/** Bytes promoted from nursery to mature space */
	var minorBytesEvacuated:Int;
	/** Last minor collection time in milliseconds */
	var lastMinorTimeMs:Float;
	/** Total time in minor collections in milliseconds */
	var totalMinorTimeMs:Float;
	/** Write barrier slow path invocations */
	var writeBarriersTriggered:Int;
}


/**
 * Garbage collector control and statistics.
 *
 * The GC uses a mark-sweep algorithm with fiber-aware stack scanning.
 * Collection is triggered automatically when allocation exceeds a threshold,
 * but can also be triggered manually.
 *
 * Example usage:
 * ```haxe
 * import fiberus.GC;
 *
 * class Main {
 *     static function main() {
 *         GC.setDebug(true);  // Enable verbose output
 *
 *         // ... allocate objects ...
 *
 *         GC.collect();  // Force collection
 *
 *         var stats = GC.stats();
 *         trace("Heap size: " + stats.currentHeapSize + " bytes");
 *     }
 * }
 * ```
 */
@:native("GC")
extern class GC {
	/**
	 * Triggers a garbage collection cycle.
	 *
	 * Performs mark and sweep phases, freeing unreachable objects.
	 * This is normally called automatically, but can be called
	 * explicitly to force collection at specific points.
	 */
	public static function collect():Void;

	/**
	 * Returns current GC statistics.
	 *
	 * The returned structure contains information about allocations,
	 * collections, timing, and fiber stack scanning.
	 */
	public static function stats():GCStats;

	/**
	 * Enables or disables GC debug output.
	 *
	 * When enabled, the GC prints information about each collection
	 * cycle to stderr, including marked/swept objects, timing,
	 * and heap size changes.
	 *
	 * Can also be enabled via the FIB_GC_DEBUG=1 environment variable.
	 *
	 * @param enabled True to enable debug output
	 */
	public static function setDebug(enabled:Bool):Void;

	/**
	 * Prints a summary of GC statistics to stderr.
	 *
	 * Useful for debugging and performance analysis.
	 */
	public static function printStats():Void;

	/**
	 * Returns a formatted string containing GC statistics.
	 *
	 * Returns the same information as printStats() but as a String
	 * instead of printing to stderr. Useful for logging or displaying
	 * in UI.
	 *
	 * @return Formatted multi-line string with GC statistics
	 */
	public static function statsString():String;

	/**
	 * Sets the allocation threshold before automatic collection.
	 *
	 * When allocations since the last collection exceed this threshold,
	 * a collection is triggered automatically.
	 *
	 * @param bytes Threshold in bytes (default: 1MB)
	 */
	public static function setThreshold(bytes:Int):Void;

	/**
	 * Gets the current allocation threshold.
	 *
	 * @return Threshold in bytes
	 */
	public static function getThreshold():Int;

	/**
	 * Enter a GC-free zone.
	 *
	 * While in a GC-free zone, this thread will not block garbage collection.
	 * The GC can proceed with stop-the-world without waiting for this thread.
	 *
	 * **Important:** While in a GC-free zone, you MUST NOT:
	 * - Allocate GC-managed objects
	 * - Access GC-managed pointers (Haxe objects, strings, arrays, etc.)
	 *
	 * This is intended for long-running native/C calls (regex matching,
	 * JSON parsing, compression, subprocess waiting, etc.) that only
	 * operate on non-GC memory.
	 *
	 * Always pair with `exitUnsafe()`.
	 *
	 * Example:
	 * ```haxe
	 * GC.enterUnsafe();
	 * // ... long-running native call ...
	 * GC.exitUnsafe();
	 * ```
	 */
	public static function enterUnsafe():Void;

	/**
	 * Exit a GC-free zone.
	 *
	 * If a GC collection is currently in progress, this will wait for it
	 * to complete before returning. After this call, the thread is back in
	 * managed mode and can safely access GC objects again.
	 */
	public static function exitUnsafe():Void;

	/**
	 * Triggers a minor (nursery) collection.
	 *
	 * This is normally called automatically when the nursery fills up,
	 * but can be called explicitly for testing or to ensure objects
	 * are promoted to mature space.
	 */
	public static function minorCollect():Void;

	/**
	 * Sets the nursery collection threshold.
	 *
	 * When nursery allocations exceed this threshold, a minor collection
	 * is triggered. Default is 6.8 MiB (85% of 8 MiB nursery).
	 * Useful for testing with smaller thresholds.
	 *
	 * @param bytes Threshold in bytes
	 */
	public static function setMinorThreshold(bytes:Int):Void;

	/**
	 * Gets the current nursery collection threshold.
	 *
	 * @return Threshold in bytes
	 */
	public static function getMinorThreshold():Int;
}

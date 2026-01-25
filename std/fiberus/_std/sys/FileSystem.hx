package sys;

import fiberus.io.FD;
import fiberus.io.OpenFlags;

/**
 * File system operations.
 * Most operations are synchronous but fast. File I/O operations use io_uring.
 */
@:coreApi
class FileSystem {
    /**
     * Check if path exists (file or directory).
     */
    public static function exists(path:String):Bool {
        var fd = FD.open(path, OpenFlags.O_RDONLY, 0);
        if (fd < 0) return false;
        FD.close(fd);
        return true;
    }
    
    /**
     * Rename/move file or directory.
     */
    public static function rename(path:String, newPath:String):Void {
        var ret:Int = untyped __fiberus__("rename(fib_string_data(", path, "), fib_string_data(", newPath, "))");
        if (ret != 0) {
            throw haxe.io.Error.Custom("Failed to rename: " + path);
        }
    }
    
    /**
     * Get file statistics.
     * TODO: Date.fromTime() codegen issue - see TODO.md
     */
    public static function stat(path:String):FileStat {
        throw haxe.io.Error.Custom("stat() not yet implemented - Date codegen issue");
        // Unreachable but needed for codegen - return empty FibDynamic
        return untyped __fiberus__("fib_anon_new()");
    }
    
    /**
     * Get absolute path.
     */
    public static function fullPath(relPath:String):String {
        var result:String = untyped __fiberus__("({ char* p = realpath(fib_string_data(", relPath, "), NULL); p ? fib_string_new(p) : NULL; })");
        if (result == null) {
            throw haxe.io.Error.Custom("Cannot resolve path: " + relPath);
        }
        return result;
    }
    
    /**
     * Get absolute path (alias for fullPath).
     */
    public static function absolutePath(relPath:String):String {
        return fullPath(relPath);
    }
    
    /**
     * Check if path is a directory.
     */
    public static function isDirectory(path:String):Bool {
        // Use stat syscall directly instead of relying on stat() method
        var fd = FD.open(path, OpenFlags.O_RDONLY, 0);
        if (fd < 0) return false;
        var mode:Int = untyped __fiberus__("({ struct stat st; fib_io_fstat(", fd, ", &st); (int)st.st_mode; })");
        FD.close(fd);
        return (mode & 0x4000) != 0;  // S_IFDIR
    }
    
    /**
     * Create a directory.
     */
    public static function createDirectory(path:String):Void {
        var ret:Int = untyped __fiberus__("mkdir(fib_string_data(", path, "), 0755)");
        if (ret != 0) {
            throw haxe.io.Error.Custom("Failed to create directory: " + path);
        }
    }
    
    /**
     * Delete a file.
     */
    public static function deleteFile(path:String):Void {
        var ret:Int = untyped __fiberus__("unlink(fib_string_data(", path, "))");
        if (ret != 0) {
            throw haxe.io.Error.Custom("Failed to delete file: " + path);
        }
    }
    
    /**
     * Delete a directory (must be empty).
     */
    public static function deleteDirectory(path:String):Void {
        var ret:Int = untyped __fiberus__("rmdir(fib_string_data(", path, "))");
        if (ret != 0) {
            throw haxe.io.Error.Custom("Failed to delete directory: " + path);
        }
    }
    
    /**
     * List directory contents.
     */
    public static function readDirectory(path:String):Array<String> {
        var result:Array<String> = [];
        // Note: dirent.h is included via gc/gc.h
        untyped __fiberus__("{ DIR* d = opendir(fib_string_data(", path, ")); if (d) { struct dirent* e; while ((e = readdir(d)) != NULL) { if (strcmp(e->d_name, \".\") != 0 && strcmp(e->d_name, \"..\") != 0) { fib_array_push(", result, ", fib_dynamic_string(fib_string_new(e->d_name))); } } closedir(d); } }");
        return result;
    }
}

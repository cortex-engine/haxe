package sys.io;

import fiberus.io.FD;
import fiberus.io.OpenFlags;

/**
 * Static file operations using io_uring for high-performance non-blocking I/O.
 * All operations suspend the calling fiber (not the OS thread).
 */
@:coreApi
class File {
    /**
     * Read entire file contents as string.
     */
    public static function getContent(path:String):String {
        var bytes = getBytes(path);
        return bytes.toString();
    }
    
    /**
     * Write string contents to file (creates or truncates).
     */
    public static function saveContent(path:String, content:String):Void {
        var bytes = haxe.io.Bytes.ofString(content);
        saveBytes(path, bytes);
    }
    
    /**
     * Read entire file contents as Bytes.
     */
    public static function getBytes(path:String):haxe.io.Bytes {
        var input = read(path, true);
        var bytes = input.readAll();
        input.close();
        return bytes;
    }
    
    /**
     * Write Bytes to file (creates or truncates).
     */
    public static function saveBytes(path:String, bytes:haxe.io.Bytes):Void {
        var output = write(path, true);
        output.writeBytes(bytes, 0, bytes.length);
        output.close();
    }
    
    /**
     * Open file for reading.
     */
    public static function read(path:String, binary:Bool = true):FileInput {
        var fd = FD.open(path, OpenFlags.O_RDONLY, 0);
        if (fd < 0) {
            throw haxe.io.Error.Custom("Failed to open file for reading: " + path + " (errno " + (-fd) + ")");
        }
        return new FileInput(fd);
    }
    
    /**
     * Open file for writing (creates or truncates).
     */
    public static function write(path:String, binary:Bool = true):FileOutput {
        var fd = FD.open(path, OpenFlags.O_WRONLY | OpenFlags.O_CREAT | OpenFlags.O_TRUNC, 420); // 0644
        if (fd < 0) {
            throw haxe.io.Error.Custom("Failed to open file for writing: " + path + " (errno " + (-fd) + ")");
        }
        return new FileOutput(fd);
    }
    
    /**
     * Open file for appending.
     */
    public static function append(path:String, binary:Bool = true):FileOutput {
        var fd = FD.open(path, OpenFlags.O_WRONLY | OpenFlags.O_CREAT | OpenFlags.O_APPEND, 420);
        if (fd < 0) {
            throw haxe.io.Error.Custom("Failed to open file for append: " + path + " (errno " + (-fd) + ")");
        }
        return new FileOutput(fd);
    }
    
    /**
     * Open file for reading and writing (creates if doesn't exist).
     */
    public static function update(path:String, binary:Bool = true):FileOutput {
        var fd = FD.open(path, OpenFlags.O_RDWR | OpenFlags.O_CREAT, 420);
        if (fd < 0) {
            throw haxe.io.Error.Custom("Failed to open file for update: " + path + " (errno " + (-fd) + ")");
        }
        return new FileOutput(fd);
    }
    
    /**
     * Copy file from source to destination.
     */
    public static function copy(srcPath:String, dstPath:String):Void {
        var bytes = getBytes(srcPath);
        saveBytes(dstPath, bytes);
    }
}

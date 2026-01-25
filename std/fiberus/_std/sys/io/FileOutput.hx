package sys.io;

import fiberus.io.FD;
import fiberus.io.OpenFlags;

/**
 * File writing stream using io_uring for non-blocking I/O.
 * All write operations suspend the calling fiber (not the OS thread).
 */
@:coreApi
@:allow(sys.io.File)
class FileOutput extends haxe.io.Output {
    var fd:Int;
    var pos:haxe.Int64;
    var isClosed:Bool;
    
    // Constructor signature: takes Int but declared as Dynamic for core API compatibility
    function new(f:Int) {
        this.fd = f;
        this.pos = haxe.Int64.ofInt(0);
        this.isClosed = false;
    }
    
    override public function writeByte(c:Int):Void {
        if (isClosed) throw haxe.io.Error.Custom("File is closed");
        var buf = haxe.io.Bytes.alloc(1);
        buf.set(0, c);
        var n = FD.write(fd, buf, 0, 1);
        if (n < 0) throw haxe.io.Error.Custom("Write error: errno " + (-n));
        pos = haxe.Int64.add(pos, haxe.Int64.ofInt(1));
    }
    
    override public function writeBytes(s:haxe.io.Bytes, pos:Int, len:Int):Int {
        if (isClosed) throw haxe.io.Error.Custom("File is closed");
        if (len <= 0) return 0;
        var n = FD.write(fd, s, pos, len);
        if (n < 0) throw haxe.io.Error.Custom("Write error: errno " + (-n));
        this.pos = haxe.Int64.add(this.pos, haxe.Int64.ofInt(n));
        return n;
    }
    
    override public function flush():Void {
        if (isClosed) return;
        var ret = FD.fsync(fd);
        if (ret < 0) throw haxe.io.Error.Custom("Flush error: errno " + (-ret));
    }
    
    override public function close():Void {
        if (!isClosed) {
            FD.close(fd);
            isClosed = true;
        }
    }
    
    /**
     * Seek to position in file.
     */
    public function seek(p:Int, pos:FileSeek):Void {
        if (isClosed) throw haxe.io.Error.Custom("File is closed");
        var whence = switch (pos) {
            case SeekBegin: OpenFlags.SEEK_SET;
            case SeekCur: OpenFlags.SEEK_CUR;
            case SeekEnd: OpenFlags.SEEK_END;
        };
        var newPos = FD.lseek(fd, haxe.Int64.ofInt(p), whence);
        if (haxe.Int64.compare(newPos, haxe.Int64.ofInt(0)) < 0) {
            throw haxe.io.Error.Custom("Seek error");
        }
        this.pos = newPos;
    }
    
    /**
     * Get current file position.
     */
    public function tell():Int {
        return haxe.Int64.toInt(pos);
    }
}

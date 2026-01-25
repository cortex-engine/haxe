package sys.io;

import fiberus.io.FD;
import fiberus.io.OpenFlags;

/**
 * File reading stream using io_uring for non-blocking I/O.
 * All read operations suspend the calling fiber (not the OS thread).
 */
@:coreApi
@:allow(sys.io.File)
class FileInput extends haxe.io.Input {
    var fd:Int;
    var pos:haxe.Int64;
    var fileSize:haxe.Int64;
    var isClosed:Bool;
    
    // Constructor signature: takes Int but declared as Dynamic for core API compatibility
    function new(f:Int) {
        this.fd = f;
        this.pos = haxe.Int64.ofInt(0);
        this.fileSize = FD.getSize(fd);
        this.isClosed = false;
    }
    
    override public function readByte():Int {
        if (isClosed) throw haxe.io.Error.Custom("File is closed");
        var buf = haxe.io.Bytes.alloc(1);
        var n = FD.read(fd, buf, 0, 1);
        if (n < 0) throw haxe.io.Error.Custom("Read error: errno " + (-n));
        if (n == 0) throw new haxe.io.Eof();
        pos = haxe.Int64.add(pos, haxe.Int64.ofInt(1));
        return buf.get(0);
    }
    
    override public function readBytes(s:haxe.io.Bytes, pos:Int, len:Int):Int {
        if (isClosed) throw haxe.io.Error.Custom("File is closed");
        if (len <= 0) return 0;
        var n = FD.read(fd, s, pos, len);
        if (n < 0) throw haxe.io.Error.Custom("Read error: errno " + (-n));
        if (n == 0) throw new haxe.io.Eof();
        this.pos = haxe.Int64.add(this.pos, haxe.Int64.ofInt(n));
        return n;
    }
    
    override public function close():Void {
        if (!isClosed) {
            FD.close(fd);
            isClosed = true;
        }
    }
    
    /**
     * Read all remaining content from the file.
     * Override needed because base class doesn't have virtual dispatch.
     */
    override public function readAll(?bufsize:Int):haxe.io.Bytes {
        if (bufsize == null) bufsize = 16384;
        
        var buf = haxe.io.Bytes.alloc(bufsize);
        var total = new haxe.io.BytesBuffer();
        try {
            while (true) {
                // Directly call our readBytes, not the base class
                var len = readBytes(buf, 0, bufsize);
                if (len == 0)
                    throw haxe.io.Error.Blocked;
                total.addBytes(buf, 0, len);
            }
        } catch (e:haxe.io.Eof) {}
        return total.getBytes();
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
    
    /**
     * Check if at end of file.
     */
    public function eof():Bool {
        return haxe.Int64.compare(pos, fileSize) >= 0;
    }
}

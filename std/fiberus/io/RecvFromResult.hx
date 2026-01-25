package fiberus.io;

/**
 * Result of a recvfrom() operation containing bytes read and sender address.
 */
class RecvFromResult {
    /** Number of bytes read, or negative errno on failure */
    public var bytesRead:Int;
    
    /** Sender IP address as string */
    public var host:String;
    
    /** Sender port number */
    public var port:Int;
    
    public function new(bytesRead:Int, host:String, port:Int) {
        this.bytesRead = bytesRead;
        this.host = host;
        this.port = port;
    }
    
    /** Check if the operation succeeded */
    public inline function isSuccess():Bool {
        return bytesRead >= 0;
    }
    
    /** Get the error code (only valid if bytesRead < 0) */
    public inline function getError():Int {
        return bytesRead < 0 ? -bytesRead : 0;
    }
}

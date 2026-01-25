package fiberus.io;

/**
 * Result of an accept() operation containing the new socket fd and peer address.
 */
class AcceptResult {
    /** New socket file descriptor, or negative errno on failure */
    public var fd:Int;
    
    /** Peer IP address as string */
    public var host:String;
    
    /** Peer port number */
    public var port:Int;
    
    public function new(fd:Int, host:String, port:Int) {
        this.fd = fd;
        this.host = host;
        this.port = port;
    }
    
    /** Check if the accept succeeded */
    public inline function isSuccess():Bool {
        return fd >= 0;
    }
    
    /** Get the error code (only valid if fd < 0) */
    public inline function getError():Int {
        return fd < 0 ? -fd : 0;
    }
}

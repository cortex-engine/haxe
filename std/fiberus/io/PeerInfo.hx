package fiberus.io;

/**
 * Socket peer/local address information.
 */
class PeerInfo {
    /** IP address as string */
    public var host:String;
    
    /** Port number */
    public var port:Int;
    
    public function new(host:String, port:Int) {
        this.host = host;
        this.port = port;
    }
    
    public function toString():String {
        return host + ":" + port;
    }
}

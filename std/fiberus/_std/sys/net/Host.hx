package sys.net;

/**
 * Hostname/IP address wrapper.
 */
@:coreApi
class Host {
    /** The hostname or IP address string */
    public var host(default, null):String;
    
    /** The IP address as an integer (0 if not resolved) */
    public var ip(default, null):Int;
    
    public function new(name:String) {
        this.host = name;
        this.ip = 0;  // TODO: Resolve to IP
    }
    
    /**
     * Get the hostname/IP as string.
     */
    public function toString():String {
        return host;
    }
    
    /**
     * Reverse DNS lookup.
     */
    public function reverse():String {
        // TODO: Implement reverse DNS
        return host;
    }
    
    /**
     * Get localhost address.
     */
    public static function localhost():String {
        return "127.0.0.1";
    }
}

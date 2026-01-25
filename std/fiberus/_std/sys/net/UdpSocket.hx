package sys.net;

import fiberus.io.FD;
import fiberus.io.OpenFlags;

/**
 * UDP Socket using io_uring for non-blocking I/O.
 */
@:coreApi
class UdpSocket extends Socket {
    public override function new() {
        super();
        FD.close(getFd());
        var newFd = FD.socket(OpenFlags.AF_INET, OpenFlags.SOCK_DGRAM, 0);
        if (newFd < 0) throw haxe.io.Error.Custom("Failed to create UDP socket: errno " + (-newFd));
        initFromFd(newFd);
    }
    
    /**
     * Send datagram to address.
     * Address.host is an Int representing IP in network byte order.
     */
    public function sendTo(buf:haxe.io.Bytes, pos:Int, len:Int, addr:Address):Int {
        // Convert IP int to string representation
        var hostStr = ipIntToString(addr.host);
        return FD.sendto(getFd(), buf, pos, len, 0, hostStr, addr.port);
    }
    
    /**
     * Receive datagram and get sender address.
     */
    public function readFrom(buf:haxe.io.Bytes, pos:Int, len:Int, addr:Address):Int {
        var result = FD.recvfrom(getFd(), buf, pos, len, 0);
        addr.host = ipStringToInt(result.host);
        addr.port = result.port;
        return result.bytesRead;
    }
    
    /**
     * Enable/disable broadcast.
     */
    public function setBroadcast(b:Bool):Void {
        FD.setsockopt(getFd(), OpenFlags.SOL_SOCKET, OpenFlags.SO_BROADCAST, b ? 1 : 0);
    }
    
    /**
     * Convert IP integer (network byte order) to dotted-decimal string.
     */
    static function ipIntToString(ip:Int):String {
        // IP is stored in network byte order (big endian)
        var a = (ip >> 24) & 0xFF;
        var b = (ip >> 16) & 0xFF;
        var c = (ip >> 8) & 0xFF;
        var d = ip & 0xFF;
        return a + "." + b + "." + c + "." + d;
    }
    
    /**
     * Convert dotted-decimal string to IP integer (network byte order).
     */
    static function ipStringToInt(ip:String):Int {
        // Simple parsing - split by dots
        var parts = ip.split(".");
        if (parts.length != 4) return 0;
        var a = Std.parseInt(parts[0]);
        var b = Std.parseInt(parts[1]);
        var c = Std.parseInt(parts[2]);
        var d = Std.parseInt(parts[3]);
        if (a == null) a = 0;
        if (b == null) b = 0;
        if (c == null) c = 0;
        if (d == null) d = 0;
        return (a << 24) | (b << 16) | (c << 8) | d;
    }
}

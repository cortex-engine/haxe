package sys.net;

import fiberus.io.FD;
import fiberus.io.OpenFlags;

/**
 * TCP Socket using io_uring for non-blocking I/O.
 * All I/O operations suspend the calling fiber (not the OS thread).
 */
@:coreApi
class Socket {
    /** Input stream for reading from the socket */
    public var input(default, null):haxe.io.Input;
    
    /** Output stream for writing to the socket */
    public var output(default, null):haxe.io.Output;
    
    /** User-defined custom data */
    public var custom:Dynamic;
    
    var fd:Int;
    var timeout:Null<Float>;
    var blocking:Bool = true;
    
    public function new() {
        fd = FD.socket(OpenFlags.AF_INET, OpenFlags.SOCK_STREAM, 0);
        if (fd < 0) throw haxe.io.Error.Custom("Failed to create socket: errno " + (-fd));
        input = new SocketInput(this);
        output = new SocketOutput(this);
    }
    
    @:allow(sys.net)
    function initFromFd(newFd:Int):Void {
        fd = newFd;
        input = new SocketInput(this);
        output = new SocketOutput(this);
    }
    
    /**
     * Close the socket.
     */
    public function close():Void {
        FD.close(fd);
    }
    
    /**
     * Read all available data as string.
     */
    public function read():String {
        var buf = new haxe.io.BytesBuffer();
        try {
            while (true) {
                var chunk = haxe.io.Bytes.alloc(4096);
                var n = FD.recv(fd, chunk, 0, 4096, 0);
                if (n <= 0) break;
                buf.addBytes(chunk, 0, n);
            }
        } catch (e:haxe.io.Eof) {}
        return buf.getBytes().toString();
    }
    
    /**
     * Write string to socket.
     */
    public function write(content:String):Void {
        var bytes = haxe.io.Bytes.ofString(content);
        var pos = 0;
        while (pos < bytes.length) {
            var n = FD.send(fd, bytes, pos, bytes.length - pos, 0);
            if (n < 0) throw haxe.io.Error.Custom("Socket write error: errno " + (-n));
            pos += n;
        }
    }
    
    /**
     * Connect to remote host. Suspends fiber until connected.
     */
    public function connect(host:Host, port:Int):Void {
        var result = FD.connect(fd, host.toString(), port);
        if (result < 0) throw haxe.io.Error.Custom("Connection failed: errno " + (-result));
    }
    
    /**
     * Start listening for connections.
     */
    public function listen(connections:Int):Void {
        var result = FD.listen(fd, connections);
        if (result < 0) throw haxe.io.Error.Custom("Listen failed: errno " + (-result));
    }
    
    /**
     * Shutdown socket.
     */
    public function shutdown(read:Bool, write:Bool):Void {
        var how = 0;
        if (read && write) how = OpenFlags.SHUT_RDWR;
        else if (read) how = OpenFlags.SHUT_RD;
        else if (write) how = OpenFlags.SHUT_WR;
        FD.shutdown(fd, how);
    }
    
    /**
     * Bind socket to local address.
     */
    public function bind(host:Host, port:Int):Void {
        // Set SO_REUSEADDR
        FD.setsockopt(fd, OpenFlags.SOL_SOCKET, OpenFlags.SO_REUSEADDR, 1);
        
        var result = FD.bind(fd, host.toString(), port);
        if (result < 0) throw haxe.io.Error.Custom("Bind failed: errno " + (-result));
    }
    
    /**
     * Accept incoming connection. Suspends fiber until connection arrives.
     */
    public function accept():Socket {
        var result = FD.accept(fd);
        if (result.fd < 0) throw haxe.io.Error.Custom("Accept failed: errno " + (-result.fd));
        var client = @:privateAccess new Socket();
        @:privateAccess client.initFromFd(result.fd);
        return client;
    }
    
    /**
     * Get peer address.
     */
    public function peer():{host:Host, port:Int} {
        var info = FD.getpeername(fd);
        return { host: new Host(info.host), port: info.port };
    }
    
    /**
     * Get local address.
     */
    public function host():{host:Host, port:Int} {
        var info = FD.getsockname(fd);
        return { host: new Host(info.host), port: info.port };
    }
    
    /**
     * Set timeout for operations.
     */
    public function setTimeout(timeout:Float):Void {
        this.timeout = timeout;
    }
    
    /**
     * Wait for data to be readable.
     * With io_uring, reads naturally block the fiber, so this is a no-op.
     */
    public function waitForRead():Void {
        // No-op - io_uring handles this
    }
    
    /**
     * Set blocking mode.
     */
    public function setBlocking(b:Bool):Void {
        blocking = b;
    }
    
    /**
     * Enable/disable TCP_NODELAY (disable Nagle algorithm).
     */
    public function setFastSend(b:Bool):Void {
        FD.setsockopt(fd, OpenFlags.IPPROTO_TCP, OpenFlags.TCP_NODELAY, b ? 1 : 0);
    }
    
    /**
     * Select on multiple sockets.
     * Note: With fibers, prefer using one fiber per socket instead.
     */
    public static function select(read:Array<Socket>, write:Array<Socket>, others:Array<Socket>,
            ?timeout:Float):{read:Array<Socket>, write:Array<Socket>, others:Array<Socket>} {
        // TODO: Implement via io_uring poll or recommend fiber-per-socket pattern
        throw new haxe.exceptions.NotImplementedException();
    }
    
    @:allow(sys.net)
    function getFd():Int {
        return fd;
    }
}

/**
 * Socket input stream.
 */
private class SocketInput extends haxe.io.Input {
    var socket:Socket;
    
    public function new(socket:Socket) {
        this.socket = socket;
    }
    
    override public function readByte():Int {
        var buf = haxe.io.Bytes.alloc(1);
        var n = FD.recv(socket.getFd(), buf, 0, 1, 0);
        if (n <= 0) throw new haxe.io.Eof();
        return buf.get(0);
    }
    
    override public function readBytes(s:haxe.io.Bytes, pos:Int, len:Int):Int {
        var n = FD.recv(socket.getFd(), s, pos, len, 0);
        if (n < 0) throw haxe.io.Error.Custom("Socket read error: errno " + (-n));
        if (n == 0) throw new haxe.io.Eof();
        return n;
    }
    
    override public function close():Void {
        socket.shutdown(true, false);
    }
}

/**
 * Socket output stream.
 */
private class SocketOutput extends haxe.io.Output {
    var socket:Socket;
    
    public function new(socket:Socket) {
        this.socket = socket;
    }
    
    override public function writeByte(c:Int):Void {
        var buf = haxe.io.Bytes.alloc(1);
        buf.set(0, c);
        var n = FD.send(socket.getFd(), buf, 0, 1, 0);
        if (n < 0) throw haxe.io.Error.Custom("Socket write error: errno " + (-n));
    }
    
    override public function writeBytes(s:haxe.io.Bytes, pos:Int, len:Int):Int {
        var n = FD.send(socket.getFd(), s, pos, len, 0);
        if (n < 0) throw haxe.io.Error.Custom("Socket write error: errno " + (-n));
        return n;
    }
    
    override public function close():Void {
        socket.shutdown(false, true);
    }
}

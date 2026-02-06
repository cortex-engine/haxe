package fiberus.io;

/**
 * Low-level file descriptor operations using io_uring.
 * All blocking operations suspend the calling fiber (not the OS thread).
 * 
 * This is the foundation for higher-level APIs like sys.io.File and sys.net.Socket.
 * Most users should prefer those higher-level APIs.
 * 
 * Error handling: Functions return negative errno values on failure.
 * Use Std.abs(result) to get the errno, or check result < 0.
 */
class FD {
    // ========================================================================
    // File Operations
    // ========================================================================
    
    /**
     * Open a file. This is synchronous (io_uring doesn't have async open).
     * @param path File path
     * @param flags Open flags (see OpenFlags)
     * @param mode File mode for creation (default 0644)
     * @return File descriptor on success, negative errno on failure
     */
    public static function open(path:String, flags:Int, mode:Int = 420):Int {
        return untyped __fiberus__("fib_io_open(fib_string_data(", path, "), ", flags, ", ", mode, ")");
    }
    
    /**
     * Close a file descriptor.
     * @return 0 on success, negative errno on failure
     */
    public static function close(fd:Int):Int {
        return untyped __fiberus__("fib_io_close(", fd, ")");
    }
    
    /**
     * Read from file descriptor. Suspends fiber until data is available.
     * @param fd File descriptor
     * @param buffer Buffer to read into
     * @param offset Offset in buffer
     * @param length Maximum bytes to read
     * @return Bytes read on success, negative errno on failure, 0 on EOF
     */
    public static function read(fd:Int, buffer:haxe.io.Bytes, offset:Int, length:Int):Int {
        return untyped __fiberus__("(int32_t)fib_io_read_managed(", fd, ", ", buffer, "->b, ", offset, ", ", length, ", -1)");
    }
    
    /**
     * Write to file descriptor. Suspends fiber until write completes.
     * @param fd File descriptor
     * @param buffer Buffer to write from
     * @param offset Offset in buffer
     * @param length Bytes to write
     * @return Bytes written on success, negative errno on failure
     */
    public static function write(fd:Int, buffer:haxe.io.Bytes, offset:Int, length:Int):Int {
        return untyped __fiberus__("(int32_t)fib_io_write_managed(", fd, ", ", buffer, "->b, ", offset, ", ", length, ", -1)");
    }
    
    /**
     * Positional read (doesn't change file position).
     * @param fileOffset Offset in file to read from
     */
    public static function pread(fd:Int, buffer:haxe.io.Bytes, offset:Int, length:Int, fileOffset:haxe.Int64):Int {
        return untyped __fiberus__("(int32_t)fib_io_read_managed(", fd, ", ", buffer, "->b, ", offset, ", ", length, ", (off_t)", fileOffset, ")");
    }
    
    /**
     * Positional write (doesn't change file position).
     * @param fileOffset Offset in file to write to
     */
    public static function pwrite(fd:Int, buffer:haxe.io.Bytes, offset:Int, length:Int, fileOffset:haxe.Int64):Int {
        return untyped __fiberus__("(int32_t)fib_io_write_managed(", fd, ", ", buffer, "->b, ", offset, ", ", length, ", (off_t)", fileOffset, ")");
    }
    
    /**
     * Seek file position.
     * @param whence 0=SEEK_SET, 1=SEEK_CUR, 2=SEEK_END
     * @return New position on success, negative errno on failure
     */
    public static function lseek(fd:Int, offset:haxe.Int64, whence:Int):haxe.Int64 {
        return untyped __fiberus__("(int64_t)fib_io_lseek(", fd, ", (off_t)", offset, ", ", whence, ")");
    }
    
    /**
     * Sync file to disk. Suspends fiber until sync completes.
     * @return 0 on success, negative errno on failure
     */
    public static function fsync(fd:Int):Int {
        return untyped __fiberus__("fib_io_fsync(", fd, ")");
    }
    
    /**
     * Get file size.
     * @return File size on success, negative errno on failure
     */
    public static function getSize(fd:Int):haxe.Int64 {
        return untyped __fiberus__("({ struct stat st; int r = fib_io_fstat(", fd, ", &st); r < 0 ? r : st.st_size; })");
    }
    
    // ========================================================================
    // Socket Operations
    // ========================================================================
    
    /**
     * Create a socket.
     * @param domain AF_INET=2, AF_INET6=10
     * @param type SOCK_STREAM=1, SOCK_DGRAM=2
     * @param protocol Usually 0
     * @return Socket fd on success, negative errno on failure
     */
    public static function socket(domain:Int, type:Int, protocol:Int):Int {
        return untyped __fiberus__("fib_io_socket(", domain, ", ", type, ", ", protocol, ")");
    }
    
    /**
     * Bind socket to address.
     * @return 0 on success, negative errno on failure
     */
    public static function bind(fd:Int, host:String, port:Int):Int {
        return untyped __fiberus__("fib_io_bind(", fd, ", fib_string_data(", host, "), ", port, ")");
    }
    
    /**
     * Start listening on socket.
     * @return 0 on success, negative errno on failure
     */
    public static function listen(fd:Int, backlog:Int):Int {
        return untyped __fiberus__("fib_io_listen(", fd, ", ", backlog, ")");
    }
    
    /**
     * Accept connection. Suspends fiber until connection arrives.
     * @return AcceptResult with fd and peer info
     */
    public static function accept(fd:Int):AcceptResult {
        var result = new AcceptResult(-1, "", 0);
        untyped __fiberus__("{ FibAddrInfo addr = {0}; int r = fib_io_accept(", fd, ", &addr); ",
            result, "->fd = r; if (r >= 0) { ", result, "->host = fib_string_new(addr.host); ", result, "->port = addr.port; } }");
        return result;
    }
    
    /**
     * Connect to remote address. Suspends fiber until connected.
     * @return 0 on success, negative errno on failure
     */
    public static function connect(fd:Int, host:String, port:Int):Int {
        return untyped __fiberus__("fib_io_connect(", fd, ", fib_string_data(", host, "), ", port, ")");
    }
    
    /**
     * Receive data from socket. Suspends fiber until data available.
     * @return Bytes received on success, negative errno on failure, 0 on connection closed
     */
    public static function recv(fd:Int, buffer:haxe.io.Bytes, offset:Int, length:Int, flags:Int):Int {
        return untyped __fiberus__("(int32_t)fib_io_recv_managed(", fd, ", ", buffer, "->b, ", offset, ", ", length, ", ", flags, ")");
    }
    
    /**
     * Send data to socket. Suspends fiber until sent.
     * @return Bytes sent on success, negative errno on failure
     */
    public static function send(fd:Int, buffer:haxe.io.Bytes, offset:Int, length:Int, flags:Int):Int {
        return untyped __fiberus__("(int32_t)fib_io_send_managed(", fd, ", ", buffer, "->b, ", offset, ", ", length, ", ", flags, ")");
    }
    
    /**
     * Receive datagram with sender address (UDP).
     */
    public static function recvfrom(fd:Int, buffer:haxe.io.Bytes, offset:Int, length:Int, flags:Int):RecvFromResult {
        var result = new RecvFromResult(0, "", 0);
        untyped __fiberus__("{ FibAddrInfo addr = {0}; ssize_t r = fib_io_recvfrom_managed(", fd, ", ", buffer, "->b, ", offset, ", ", length, ", ", flags, ", &addr); ",
            result, "->bytesRead = (int32_t)r; ", result, "->host = fib_string_new(addr.host); ", result, "->port = addr.port; }");
        return result;
    }
    
    /**
     * Send datagram to address (UDP).
     */
    public static function sendto(fd:Int, buffer:haxe.io.Bytes, offset:Int, length:Int, flags:Int, host:String, port:Int):Int {
        return untyped __fiberus__("(int32_t)fib_io_sendto_managed(", fd, ", ", buffer, "->b, ", offset, ", ", length, ", ", flags, ", fib_string_data(", host, "), ", port, ")");
    }
    
    /**
     * Poll fd for readability/writability. Suspends fiber until ready or timeout.
     * Uses io_uring IORING_OP_POLL_ADD internally.
     * @param fd File descriptor to poll
     * @param events Event mask (OpenFlags.POLLIN, OpenFlags.POLLOUT, or both OR'd)
     * @param timeoutMs Timeout in milliseconds (-1 = infinite, 0 = non-blocking)
     * @return Positive revents mask on success, 0 on timeout, negative errno on error
     */
    public static function poll(fd:Int, events:Int, timeoutMs:Int):Int {
        return untyped __fiberus__("fib_io_poll_fd(", fd, ", ", events, ", ", timeoutMs, ")");
    }

    /**
     * Shutdown socket.
     * @param how 0=read, 1=write, 2=both
     */
    public static function shutdown(fd:Int, how:Int):Int {
        return untyped __fiberus__("fib_io_shutdown(", fd, ", ", how, ")");
    }
    
    /**
     * Set socket option.
     */
    public static function setsockopt(fd:Int, level:Int, optname:Int, optval:Int):Int {
        return untyped __fiberus__("fib_io_setsockopt(", fd, ", ", level, ", ", optname, ", ", optval, ")");
    }
    
    /**
     * Get socket option.
     */
    public static function getsockopt(fd:Int, level:Int, optname:Int):Int {
        return untyped __fiberus__("fib_io_getsockopt(", fd, ", ", level, ", ", optname, ")");
    }
    
    /**
     * Get peer address info.
     */
    public static function getpeername(fd:Int):PeerInfo {
        var result = new PeerInfo("", 0);
        untyped __fiberus__("{ FibAddrInfo addr = {0}; fib_io_getpeername(", fd, ", &addr); ",
            result, "->host = fib_string_new(addr.host); ", result, "->port = addr.port; }");
        return result;
    }
    
    /**
     * Get local address info.
     */
    public static function getsockname(fd:Int):PeerInfo {
        var result = new PeerInfo("", 0);
        untyped __fiberus__("{ FibAddrInfo addr = {0}; fib_io_getsockname(", fd, ", &addr); ",
            result, "->host = fib_string_new(addr.host); ", result, "->port = addr.port; }");
        return result;
    }
}

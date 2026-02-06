package fiberus.io;

/**
 * File open flags matching POSIX constants.
 * Use bitwise OR to combine flags: OpenFlags.O_RDWR | OpenFlags.O_CREAT
 */
class OpenFlags {
    /** Open for reading only */
    public static inline var O_RDONLY:Int = 0;
    
    /** Open for writing only */
    public static inline var O_WRONLY:Int = 1;
    
    /** Open for reading and writing */
    public static inline var O_RDWR:Int = 2;
    
    /** Create file if it doesn't exist */
    public static inline var O_CREAT:Int = 64;
    
    /** Fail if file exists (with O_CREAT) */
    public static inline var O_EXCL:Int = 128;
    
    /** Truncate file to zero length */
    public static inline var O_TRUNC:Int = 512;
    
    /** Append to end of file */
    public static inline var O_APPEND:Int = 1024;
    
    /** Non-blocking mode (rarely needed with fiber I/O) */
    public static inline var O_NONBLOCK:Int = 2048;
    
    /** Synchronous I/O */
    public static inline var O_SYNC:Int = 1052672;
    
    // ========================================================================
    // Seek whence values
    // ========================================================================
    
    /** Seek from beginning of file */
    public static inline var SEEK_SET:Int = 0;
    
    /** Seek from current position */
    public static inline var SEEK_CUR:Int = 1;
    
    /** Seek from end of file */
    public static inline var SEEK_END:Int = 2;
    
    // ========================================================================
    // Socket constants
    // ========================================================================
    
    /** IPv4 address family */
    public static inline var AF_INET:Int = 2;
    
    /** IPv6 address family */
    public static inline var AF_INET6:Int = 10;
    
    /** Stream socket (TCP) */
    public static inline var SOCK_STREAM:Int = 1;
    
    /** Datagram socket (UDP) */
    public static inline var SOCK_DGRAM:Int = 2;
    
    /** SOL_SOCKET level */
    public static inline var SOL_SOCKET:Int = 1;
    
    /** TCP protocol level */
    public static inline var IPPROTO_TCP:Int = 6;
    
    /** SO_REUSEADDR option */
    public static inline var SO_REUSEADDR:Int = 2;
    
    /** SO_BROADCAST option */
    public static inline var SO_BROADCAST:Int = 6;
    
    /** SO_KEEPALIVE option */
    public static inline var SO_KEEPALIVE:Int = 9;
    
    /** SO_REUSEPORT option (allow multiple sockets to bind to the same port) */
    public static inline var SO_REUSEPORT:Int = 15;
    
    /** TCP_NODELAY option (disable Nagle) */
    public static inline var TCP_NODELAY:Int = 1;
    
    // ========================================================================
    // Send/Recv flags
    // ========================================================================
    
    /** Non-blocking send/recv */
    public static inline var MSG_DONTWAIT:Int = 64;
    
    /** Peek at incoming data without consuming */
    public static inline var MSG_PEEK:Int = 2;
    
    /** Wait for full request or error */
    public static inline var MSG_WAITALL:Int = 256;
    
    // ========================================================================
    // Poll event masks
    // ========================================================================
    
    /** Data available for reading */
    public static inline var POLLIN:Int = 1;
    
    /** Writing possible */
    public static inline var POLLOUT:Int = 4;
    
    /** Error condition */
    public static inline var POLLERR:Int = 8;
    
    /** Hang up */
    public static inline var POLLHUP:Int = 16;
    
    // ========================================================================
    // Errno values (returned as negative from I/O operations)
    // ========================================================================
    
    /** Resource temporarily unavailable (try again) */
    public static inline var EAGAIN:Int = 11;
    
    /** Operation would block (same as EAGAIN on Linux) */
    public static inline var EWOULDBLOCK:Int = 11;
    
    /** Connection reset by peer */
    public static inline var ECONNRESET:Int = 104;
    
    /** Broken pipe */
    public static inline var EPIPE:Int = 32;
    
    /** Connection refused */
    public static inline var ECONNREFUSED:Int = 111;
    
    /** Operation timed out */
    public static inline var ETIMEDOUT:Int = 110;

    // ========================================================================
    // Shutdown how values
    // ========================================================================
    
    /** Shutdown read side */
    public static inline var SHUT_RD:Int = 0;
    
    /** Shutdown write side */
    public static inline var SHUT_WR:Int = 1;
    
    /** Shutdown both sides */
    public static inline var SHUT_RDWR:Int = 2;
}

/* This file is part of unscd, a complete nscd replacement.
 * Copyright (C) 2007 Denys Vlasenko. Licensed under the GPL version 2. */

/* unscd is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; version 2 of the License.
 *
 * unscd is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You can download the GNU General Public License from the GNU website
 * at http://www.gnu.org/ or write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*
Build instructions:

gcc -Wall -Wunused-parameter -Os -o nscd nscd.c

gcc -fomit-frame-pointer -Wl,--sort-section -Wl,alignment -Wl,--sort-common
      -Os -o nscd nscd.c

Description:

nscd problems are not exactly unheard of. Over the years, there were
quite a bit of bugs in it. This leads people to invent babysitters
which restart crashed/hung nscd. This is ugly.

After looking at nscd source in glibc I arrived to the conclusion
that its design is contributing to this significantly. Even if nscd's
code is 100.00% perfect and bug-free, it can still suffer from bugs
in libraries it calls.

As designed, it's a multithreaded program which calls NSS libraries.
These libraries are not part of libc, they may be provided
by third-party projects (samba, ldap, you name it).

Thus nscd cannot be sure that libraries it calls do not have memory
or file descriptor leaks and other bugs.

Since nscd is multithreaded program with single shared cache,
any resource leak in any NSS library has cumulative effect.
Even if a NSS library leaks a file descriptor 0.01% of the time,
this will make nscd crash or hang after some time.

Of course bugs in NSS .so modules should be fixed, but meanwhile
I do want nscd which does not crash or lock up.

So I went ahead and wrote a replacement.

It is a single-threaded server process which offloads all NSS
lookups to worker children (not threads, but fully independent
processes). Cache hits are handled by parent. Only cache misses
start worker children. This design is immune against
resource leaks and hangs in NSS libraries.

It is also many times smaller.

Currently (v0.36) it emulates glibc nscd pretty closely
(handles same command line flags and config file), and is moderately tested.

Please note that as of 2008-08 it is not in wide use (yet?).
If you have trouble compiling it, see an incompatibility with
"standard" one or experience hangs/crashes, please report it to
vda.linux@googlemail.com

***********************************************************************/

/* Make struct ucred appear in sys/socket.h */
#define _GNU_SOURCE 1
/* For all good things */
#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdarg.h>
#include <unistd.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <time.h>
#include <netdb.h>
#include <pwd.h>
#include <grp.h>
#include <getopt.h>
#include <syscall.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/poll.h>
#include <sys/un.h>
/* For INT_MAX */
#include <limits.h>
/* For inet_ntoa (for debug build only) */
#include <arpa/inet.h>

/*
 * 0.21 add SEGV reporting to worker
 * 0.22 don't do freeaddrinfo() in GETAI worker, it's crashy
 * 0.23 add parameter parsing
 * 0.24 add conf file parsing, not using results yet
 * 0.25 used some of conf file settings (not tested)
 * 0.26 almost all conf file settings are wired up
 * 0.27 a bit more of almost all conf file settings are wired up
 * 0.28 optimized cache aging
 * 0.29 implemented invalidate and shutdown options
 * 0.30 fixed buglet (sizeof(ptr) != sizeof(array))
 * 0.31 reduced client_info by one member
 * 0.32 fix nttl/size defaults; simpler check for worker child in main()
 * 0.33 tweak includes so that it builds on my new machine (64-bit userspace);
 *      do not die on unknown service name, just warn
 *      ("services" is a new service we don't support)
 * 0.34 create /var/run/nscd/nscd.pid pidfile like glibc nscd 2.8 does;
 *      delay setuid'ing itself to server-user after log and pidfile are open
 * 0.35 readlink /proc/self/exe and use result if execing /proc/self/exe fails
 * 0.36 excercise extreme paranoia handling server-user option;
 *      a little bit more verbose logging:
 *      L_DEBUG2 log level added, use debug-level 7 to get it
 * 0.37 users reported over-zealous "detected change in /etc/passwd",
 *      apparently stat() returns random garbage in unused padding
 *      on some systems. Made the check less paranoid.
 * 0.38 log POLLHUP better
 * 0.39 log answers to client better, log getpwnam in the worker,
 *      pass debug level value down to worker.
 * 0.40   fix handling of shutdown and invalidate requests;
 *        fix bug with answer written in several pieces
 * 0.40.1 set hints.ai_socktype = SOCK_STREAM in GETAI request
 * 0.41   eliminate double caching of two near-simultaneous identical requests -
 *        EXPERIMENTAL
 * 0.42   execute /proc/self/exe by link name first (better comm field)
 * 0.43   fix off-by-one error in setgroups
 * 0.44   make -d[ddd] bump up debug - easier to explain to users
 *        how to produce detailed log (no nscd.conf tweaking)
 * 0.45   Fix out-of-bounds array access and log/pid file permissions -
 *        thanks to Sebastian Krahmer (krahmer AT suse.de)
 * 0.46   fix a case when we forgot to remove a future entry on worker failure
 * 0.47   fix nscd without -d to not bump debug level
 */
#define PROGRAM_VERSION "0.47"

#define DEBUG_BUILD 1


/*
** Generic helpers
*/

#define ARRAY_SIZE(x) ((unsigned)(sizeof(x) / sizeof((x)[0])))

#define NORETURN __attribute__ ((__noreturn__))


#ifdef MY_CPU_HATES_CHARS
typedef int smallint;
#else
typedef signed char smallint;
#endif


enum {
	L_INFO   = (1 << 0),
	L_DEBUG  = ((1 << 1) * DEBUG_BUILD),
	L_DEBUG2 = ((1 << 2) * DEBUG_BUILD),
	L_DUMP   = ((1 << 3) * DEBUG_BUILD),
	L_ALL    = 0xf,
	D_DAEMON = (1 << 6),
	D_STAMP  = (1 << 5),
};

static smallint debug = D_DAEMON;

static void verror(const char *s, va_list p, const char *strerr)
{
	char msgbuf[1024];
	int sz, rem, strerr_len;
	struct timeval tv;

	sz = 0;
	if (debug & D_STAMP) {
		gettimeofday(&tv, NULL);
		sz = sprintf(msgbuf, "%02u:%02u:%02u.%05u ",
			(unsigned)((tv.tv_sec / (60*60)) % 24),
			(unsigned)((tv.tv_sec / 60) % 60),
			(unsigned)(tv.tv_sec % 60),
			(unsigned)(tv.tv_usec / 10));
	}
	rem = sizeof(msgbuf) - sz;
	sz += vsnprintf(msgbuf + sz, rem, s, p);
	rem = sizeof(msgbuf) - sz; /* can be negative after this! */

	if (strerr) {
		strerr_len = strlen(strerr);
		if (rem >= strerr_len + 4) { /* ": STRERR\n\0" */
			msgbuf[sz++] = ':';
			msgbuf[sz++] = ' ';
			strcpy(msgbuf + sz, strerr);
			sz += strerr_len;
		}
	}
	if (rem >= 2) {
		msgbuf[sz++] = '\n';
		msgbuf[sz] = '\0';
	}
	fflush(NULL);
	fputs(msgbuf, stderr);
}

static void error(const char *msg, ...)
{
	va_list p;
	va_start(p, msg);
	verror(msg, p, NULL);
	va_end(p);
}

static void error_and_die(const char *msg, ...) NORETURN;
static void error_and_die(const char *msg, ...)
{
	va_list p;
	va_start(p, msg);
	verror(msg, p, NULL);
	va_end(p);
	_exit(1);
}

static void perror_and_die(const char *msg, ...) NORETURN;
static void perror_and_die(const char *msg, ...)
{
	va_list p;
	va_start(p, msg);
	/* Guard against "<error message>: Success" */
	verror(msg, p, errno ? strerror(errno) : NULL);
	va_end(p);
	_exit(1);
}

static void nscd_log(int mask, const char *msg, ...)
{
	if (debug & mask) {
		va_list p;
		va_start(p, msg);
		verror(msg, p, NULL);
		va_end(p);
	}
}

#define log(lvl, ...) do { if (lvl) nscd_log(lvl, __VA_ARGS__); } while (0)

#if DEBUG_BUILD
static void dump(const void *ptr, int len)
{
	char text[18];
	const unsigned char *buf;
	char *p;

	if (!(debug & L_DUMP))
		return;

	buf = ptr;
	while (len > 0) {
		int chunk = ((len >= 16) ? 16 : len);
		fprintf(stderr,
			"%02x %02x %02x %02x %02x %02x %02x %02x "
			"%02x %02x %02x %02x %02x %02x %02x %02x " + (16-chunk) * 5,
			buf[0], buf[1], buf[2], buf[3], buf[4], buf[5], buf[6], buf[7],
			buf[8], buf[9],buf[10],buf[11],buf[12],buf[13],buf[14],buf[15]
		);
		fprintf(stderr, "%*s", (16-chunk) * 3, "");
		len -= chunk;
		p = text;
		do {
			unsigned char c = *buf++;
			*p++ = (c >= 32 && c < 127 ? c : '.');
		} while (--chunk);
		*p++ = '\n';
		*p = '\0';
		fputs(text, stderr);
	}
}
#else
void dump(const void *ptr, int len);
#endif

#define hex_dump(p,n) do { if (L_DUMP) dump(p,n); } while (0)

static int xopen3(const char *pathname, int flags, int mode)
{
	int fd = open(pathname, flags, mode);
	if (fd < 0)
		perror_and_die("open");
	return fd;
}

static void xpipe(int *fds)
{
	if (pipe(fds) < 0)
		perror_and_die("pipe");
}

static void xexecve(const char *filename, char **argv, char **envp) NORETURN;
static void xexecve(const char *filename, char **argv, char **envp)
{
	execve(filename, argv, envp);
	perror_and_die("cannot re-exec %s", filename);
}

static void ndelay_on(int fd)
{
	int fl = fcntl(fd, F_GETFL);
	if (fl < 0)
		perror_and_die("F_GETFL");
	if (fcntl(fd, F_SETFL, fl | O_NONBLOCK) < 0)
		perror_and_die("setting O_NONBLOCK");
}

static void close_on_exec(int fd)
{
	if (fcntl(fd, F_SETFD, FD_CLOEXEC) < 0)
		perror_and_die("setting FD_CLOEXEC");
}

static unsigned monotonic_ms(void)
{
	struct timespec ts;
	if (syscall(__NR_clock_gettime, CLOCK_MONOTONIC, &ts))
		perror_and_die("clock_gettime(MONOTONIC)");
	return ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static unsigned strsize(const char *str)
{
	return strlen(str) + 1;
}

static unsigned strsize_aligned4(const char *str)
{
	return (strlen(str) + 1 + 3) & (~3);
}

static ssize_t safe_read(int fd, void *buf, size_t count)
{
	ssize_t n;
	do {
		n = read(fd, buf, count);
	} while (n < 0 && errno == EINTR);
	return n;
}

static ssize_t full_read(int fd, void *buf, size_t len)
{
	ssize_t cc;
	ssize_t total;
	total = 0;
	while (len) {
		cc = safe_read(fd, buf, len);
		if (cc < 0)
			return cc;      /* read() returns -1 on failure. */
		if (cc == 0)
			break;
		buf = ((char *)buf) + cc;
		total += cc;
		len -= cc;
	}
	return total;
}

/* unused
static void xsafe_read(int fd, void *buf, size_t len)
{
	if (len != safe_read(fd, buf, len))
		perror_and_die("short read");
}
static void xfull_read(int fd, void *buf, size_t len)
{
	if (len != full_read(fd, buf, len))
		perror_and_die("short read");
}
*/

static ssize_t safe_write(int fd, const void *buf, size_t count)
{
	ssize_t n;
	do {
		n = write(fd, buf, count);
	} while (n < 0 && errno == EINTR);
	return n;
}

static ssize_t full_write(int fd, const void *buf, size_t len)
{
	ssize_t cc;
	ssize_t total;

	total = 0;
	while (len) {
		cc = safe_write(fd, buf, len);
		if (cc < 0)
			return cc;      /* write() returns -1 on failure. */
		total += cc;
		buf = ((const char *)buf) + cc;
		len -= cc;
	}
	return total;
}

static void xsafe_write(int fd, const void *buf, size_t count)
{
	if (count != safe_write(fd, buf, count))
		perror_and_die("short write of %ld bytes", (long)count);
}
static void xfull_write(int fd, const void *buf, size_t count)
{
	if (count != full_write(fd, buf, count))
		perror_and_die("short write of %ld bytes", (long)count);
}

static void xmovefd(int from_fd, int to_fd)
{
	if (from_fd != to_fd) {
		if (dup2(from_fd, to_fd) < 0)
			perror_and_die("dup2");
		close(from_fd);
	}
}

static unsigned getnum(const char *str)
{
	if (str[0] >= '0' && str[0] <= '9') {
		char *p;
		unsigned long l = strtoul(str, &p, 10);
		/* must not overflow int even after x1000 */
		if (!*p && l <= INT_MAX / 1000)
			return l;
	}
	error_and_die("malformed or too big number '%s'", str);
};

static char *skip_whitespace(const char *s)
{
	/* NB: isspace('\0') returns 0 */
	while (isspace(*s)) ++s;
	return (char *) s;
}

static char *skip_non_whitespace(const char *s)
{
	while (*s && !isspace(*s)) ++s;
	return (char *) s;
}

static void *xmalloc(unsigned sz)
{
	void *p = malloc(sz);
	if (!p)
		error_and_die("out of memory");
	return p;
}

static void *xzalloc(unsigned sz)
{
	void *p = xmalloc(sz);
	memset(p, 0, sz);
	return p;
}

static void *xrealloc(void *p, unsigned size)
{
	p = realloc(p, size);
	if (!p)
		error_and_die("out of memory");
	return p;
}

static const char *xstrdup(const char *str)
{
	const char *p = strdup(str);
	if (!p)
		error_and_die("out of memory");
	return p;
}


/*
** Config data
*/

enum {
	SRV_PASSWD,
	SRV_GROUP,
	SRV_HOSTS,
};

static const char srv_name[3][7] = {
	"passwd",
	"group",
	"hosts"
};

static struct {
	const char *logfile;
	const char *user;
	smallint srv_enable[3];
	smallint check_files[3];
	unsigned pttl[3];
	unsigned nttl[3];
	unsigned size[3];
} config = {
	/* We try to closely mimic glibc nscd */
	.logfile     = NULL, /* default is to not have a log file */
	.user        = NULL,
	.srv_enable  = { 0, 0, 0 },
	.check_files = { 1, 1, 1 },
	.pttl        = { 3600, 3600, 3600 },
	.nttl        = { 20, 60, 20 },
	/* huh, what is the default cache size in glibc nscd? */
	.size        = { 256 * 8 / 3, 256 * 8 / 3, 256 * 8 / 3 },
};

static const char default_conffile[] = "/etc/nscd.conf";
static const char *self_exe_points_to = "/proc/self/exe";


/*
** Clients, workers machinery
*/

/* Header common to all requests */
#define USER_REQ_STRUCT \
	uint32_t version; /* Version number of the daemon interface */ \
	uint32_t type;    /* Service requested */ \
	uint32_t key_len; /* Key length */

typedef struct user_req_header {
	USER_REQ_STRUCT
} user_req_header;

enum {
	NSCD_VERSION = 2,
	MAX_USER_REQ_SIZE = 1024,
	USER_HDR_SIZE = sizeof(user_req_header),
	/* DNS queries time out after 20 seconds,
	 * we will allow for a bit more */
	WORKER_TIMEOUT_SEC = 30,
	CLIENT_TIMEOUT_MS = 100,
	SMALL_POLL_TIMEOUT_MS = 200,
};

typedef struct user_req {
	union {
		struct { /* as came from client */
			USER_REQ_STRUCT
		};
		struct { /* when stored in cache, overlaps .version */
			unsigned refcount:8;
			/* (timestamp24 * 256) == timestamp in ms */
			unsigned timestamp24:24;
		};
	};
	char reqbuf[MAX_USER_REQ_SIZE - USER_HDR_SIZE];
} user_req;

/* Compile-time check for correct size */
struct BUG_wrong_user_req_size {
	char BUG_wrong_user_req_size[sizeof(user_req) == MAX_USER_REQ_SIZE ? 1 : -1];
};

enum {
	GETPWBYNAME,
	GETPWBYUID,
	GETGRBYNAME,
	GETGRBYGID,
	GETHOSTBYNAME,
	GETHOSTBYNAMEv6,
	GETHOSTBYADDR,
	GETHOSTBYADDRv6,
	SHUTDOWN,               /* Shut the server down */
	GETSTAT,                /* Get the server statistic */
	INVALIDATE,             /* Invalidate one special cache */
	GETFDPW,
	GETFDGR,
	GETFDHST,
	GETAI,
	INITGROUPS,
	GETSERVBYNAME,
	GETSERVBYPORT,
	GETFDSERV,
	LASTREQ
};
#if DEBUG_BUILD
static const char *const typestr[] = {
	"GETPWBYNAME",     /* done */
	"GETPWBYUID",      /* done */
	"GETGRBYNAME",     /* done */
	"GETGRBYGID",      /* done */
	"GETHOSTBYNAME",   /* done */
	"GETHOSTBYNAMEv6", /* done */
	"GETHOSTBYADDR",   /* done */
	"GETHOSTBYADDRv6", /* done */
	"SHUTDOWN",        /* done */
	"GETSTAT",         /* info? */
	"INVALIDATE",      /* done */
	/* won't do: nscd passes a name of shmem segment
	 * which client can map and "see" the db */
	"GETFDPW",
	"GETFDGR",         /* won't do */
	"GETFDHST",        /* won't do */
	"GETAI",           /* done */
	"INITGROUPS",      /* done */
	"GETSERVBYNAME",   /* prio 3 (no caching?) */
	"GETSERVBYPORT",   /* prio 3 (no caching?) */
	"GETFDSERV"        /* won't do */
};
#else
extern const char *const typestr[];
#endif
static const smallint type_to_srv[] = {
	[GETPWBYNAME     ] = SRV_PASSWD,
	[GETPWBYUID      ] = SRV_PASSWD,
	[GETGRBYNAME     ] = SRV_GROUP,
	[GETGRBYGID      ] = SRV_GROUP,
	[GETHOSTBYNAME   ] = SRV_HOSTS,
	[GETHOSTBYNAMEv6 ] = SRV_HOSTS,
	[GETHOSTBYADDR   ] = SRV_HOSTS,
	[GETHOSTBYADDRv6 ] = SRV_HOSTS,
	[GETAI           ] = SRV_HOSTS,
	[INITGROUPS      ] = SRV_GROUP,
};

static int unsupported_ureq_type(unsigned type)
{
	if (type == GETAI) return 0;
	if (type == INITGROUPS) return 0;
	if (type == GETSTAT) return 1;
	if (type > INVALIDATE) return 1;
	return 0;
}


typedef struct client_info {
	/* if client_fd != 0, we are waiting for the reply from worker
	 * on pfd[i].fd, and client_fd is saved client's fd
	 * (we need to put it back into pfd[i].fd later) */
	int client_fd;
	unsigned bytecnt;       /* bytes read from client */
	unsigned bufidx;        /* buffer# in global client_buf[] */
	unsigned started_ms;
	unsigned respos;        /* response */
	user_req *resptr;       /* response */
	user_req **cache_pp;    /* cache entry address */
	user_req *ureq;         /* request (points to client_buf[x]) */
} client_info;

static unsigned g_now_ms;
static int min_closed = INT_MAX;
static int cnt_closed = 0;
static int num_clients = 2; /* two listening sockets are "clients" too */

/* We read up to max_reqnum requests in parallel */
static unsigned max_reqnum = 14;
static int next_buf;
static char          (*client_buf)[MAX_USER_REQ_SIZE];
static char          *busy_cbuf;
static struct pollfd *pfd;
static client_info   *cinfo;

/* Request, response and cache data structures:
 *
 * cache[] (defined later):
 * cacheline_t cache[cache_size] array, or in other words,
 * user_req* cache[cache_size][8] array.
 * Every client request is hashed, hash value determines which cache[x]
 * will have the response stored in one of its 8 elements.
 * Cache entries have this format: request, then padding to 32 bits,
 * then the response.
 * Addresses in cache[x][y] may be NULL or:
 * (&client_buf[z]) & 1: the cache miss is in progress ("future entry"):
 * "the data is not in the cache (yet), wait for it to appear"
 * (&client_buf[z]) & 3: the cache miss is in progress and other clients
 * also want the same data ("shared future entry")
 * else (non-NULL but low two bits are 0): cached data in malloc'ed block
 *
 * Each of these is a [max_reqnum] sized array:
 * pfd[i] - given to poll() to wait for requests and replies.
 *      .fd: first two pfd[i]: listening Unix domain sockets, else
 *      .fd: open fd to a client, for reading client's request, or
 *      .fd: open fd to a worker, to send request and get response back
 * cinfo[i] - auxiliary client data for pfd[i]
 *      .client_fd: open fd to a client, in case we already had read its
 *          request and got a cache miss, and created a worker or
 *          wait for another client's worker.
 *          Otherwise, it's 0 and client's fd is in pfd[i].fd
 *      .bufidx: index in client_buf[] we store client's request in
 *      .bytecnt: size of the request
 *      .started_ms: used to time out unresponsive clients
 *      .respos:
 *      .resptr:
 *      .cache_pp: &cache[x][y] where the response is, or will be stored.
 *      .ureq:
 * When a client has received its reply (or otherwise closed (timeout etc)),
 * corresponding pfd[i] and cinfo[i] are removed by shifting [i+1], [i+2] etc
 * elements down, so that both arrays never have free holes.
 * [num_clients] is always the first free element.
 *
 * Each of these also is a [max_reqnum] sized array, but indexes
 * do not correspond directly to pfd[i] and cinfo[i]:
 * client_buf[n][MAX_USER_REQ_SIZE] - buffers we read client requests into
 * busy_cbuf[n] - bool flags marking busy client_buf[]
 */
/* Possible reductions:
 * fd, bufidx - uint8_t
 * started_ms -> uint16_t started_s
 * ureq - eliminate (derivable from bufidx?)
 */

/* Are special bits 0? is it a true cached entry? */
#define CACHED_ENTRY(p)     ( ((long)(p) & 3) == 0 )
/* Are special bits 11? is it a shared future cache entry? */
#define CACHE_SHARED(p)     ( ((long)(p) & 3) == 3 )
/* Return a ptr with special bits cleared (used for accessing data) */
#define CACHE_PTR(p)        ( (void*) ((long)(p) & ~(long)3) )
/* Return a ptr with special bits set to x1: make future cache entry ptr */
#define MAKE_FUTURE_PTR(p)  ( (void*) ((long)(p) | 1) )
/* Modify ptr, set special bits to 11: shared future cache entry */
#define MARK_PTR_SHARED(pp) ( *(long*)(pp) |= 3 )

static inline unsigned ureq_size(const user_req *ureq)
{
	return sizeof(user_req_header) + ureq->key_len;
}

static unsigned cache_age(const user_req *ureq)
{
	if (!CACHED_ENTRY(ureq))
		return 0;
	return (uint32_t) (g_now_ms - (ureq->timestamp24 << 8));
}

static void set_cache_timestamp(user_req *ureq)
{
	ureq->timestamp24 = g_now_ms >> 8;
}

static int alloc_buf_no(void)
{
	int n = next_buf;
	do {
		int cur = next_buf;
		next_buf = (next_buf + 1) % max_reqnum;
		if (!busy_cbuf[cur]) {
			busy_cbuf[cur] = 1;
			return cur;
		}
	} while (next_buf != n);
	error_and_die("no free bufs?!");
}

static inline void *bufno2buf(int i)
{
	return client_buf[i];
}

static void close_client(unsigned i)
{
	log(L_DEBUG, "closing client %u (fd %u,%u)", i, pfd[i].fd, cinfo[i].client_fd);
	/* Paranoia. We had nasty bugs where client was closed twice. */
	if (pfd[i].fd == 0) ////
		return;
	close(pfd[i].fd);
	if (cinfo[i].client_fd && cinfo[i].client_fd != pfd[i].fd)
		close(cinfo[i].client_fd);
	pfd[i].fd = 0; /* flag as unused (coalescing needs this) */
	busy_cbuf[cinfo[i].bufidx] = 0;
	cnt_closed++;
	if (i < min_closed)
		min_closed = i;
}


/*
** nscd API <-> C API conversion
*/

typedef struct response_header {
	uint32_t version_or_size;
	int32_t found;
	char body[0];
} response_header;

typedef struct initgr_response_header {
	uint32_t version_or_size;
	int32_t found;
	int32_t ngrps;
	/* code assumes gid_t == int32, let's check that */
	int32_t gid[sizeof(gid_t) == sizeof(int32_t) ? 0 : -1];
	/* char user_str[as_needed]; */
} initgr_response_header;

static initgr_response_header *obtain_initgroups(const char *username)
{
	struct initgr_response_header *resp;
	struct passwd *pw;
	enum { MAGIC_OFFSET = sizeof(*resp) / sizeof(int32_t) };
	unsigned sz;
	int ngroups;

	pw = getpwnam(username);
	if (!pw) {
		resp = xzalloc(8);
		resp->version_or_size = sizeof(*resp);
		/*resp->found = 0;*/
		/*resp->ngrps = 0;*/
		goto ret;
	}

	/* getgrouplist may be very expensive, it's much better to allocate
	 * a bit more than to run getgrouplist twice */
	ngroups = 128;
	resp = NULL;
	do {
		sz = sizeof(*resp) + sizeof(resp->gid[0]) * ngroups;
		resp = xrealloc(resp, sz);
	} while (getgrouplist(username, pw->pw_gid, (gid_t*) &resp->gid, &ngroups) == -1);
	log(L_DEBUG, "ngroups=%d", ngroups);

	sz = sizeof(*resp) + sizeof(resp->gid[0]) * ngroups;
	/* resp = xrealloc(resp, sz); - why bother */
	resp->version_or_size = sz;
	resp->found = 1;
	resp->ngrps = ngroups;
 ret:
	return resp;
}

typedef struct pw_response_header {
	uint32_t version_or_size;
	int32_t found;
	int32_t pw_name_len;
	int32_t pw_passwd_len;
	int32_t pw_uid;
	int32_t pw_gid;
	int32_t pw_gecos_len;
	int32_t pw_dir_len;
	int32_t pw_shell_len;
	/* char pw_name[pw_name_len]; */
	/* char pw_passwd[pw_passwd_len]; */
	/* char pw_gecos[pw_gecos_len]; */
	/* char pw_dir[pw_dir_len]; */
	/* char pw_shell[pw_shell_len]; */
} pw_response_header;

static pw_response_header *marshal_passwd(struct passwd *pw)
{
	char *p;
	pw_response_header *resp;
	unsigned pw_name_len;
	unsigned pw_passwd_len;
	unsigned pw_gecos_len;
	unsigned pw_dir_len;
	unsigned pw_shell_len;
	unsigned sz = sizeof(*resp);
	if (pw) {
		sz += (pw_name_len = strsize(pw->pw_name));
		sz += (pw_passwd_len = strsize(pw->pw_passwd));
		sz += (pw_gecos_len = strsize(pw->pw_gecos));
		sz += (pw_dir_len = strsize(pw->pw_dir));
		sz += (pw_shell_len = strsize(pw->pw_shell));
	}
	resp = xzalloc(sz);
	resp->version_or_size = sz;
	if (!pw) {
		/*resp->found = 0;*/
		goto ret;
	}
	resp->found = 1;
	resp->pw_name_len = pw_name_len;
	resp->pw_passwd_len = pw_passwd_len;
	resp->pw_uid = pw->pw_uid;
	resp->pw_gid = pw->pw_gid;
	resp->pw_gecos_len = pw_gecos_len;
	resp->pw_dir_len = pw_dir_len;
	resp->pw_shell_len = pw_shell_len;
	p = (char*)(resp + 1);
	strcpy(p, pw->pw_name); p += pw_name_len;
	strcpy(p, pw->pw_passwd); p += pw_passwd_len;
	strcpy(p, pw->pw_gecos); p += pw_gecos_len;
	strcpy(p, pw->pw_dir); p += pw_dir_len;
	strcpy(p, pw->pw_shell); p += pw_shell_len;
	log(L_DEBUG, "sz:%u realsz:%u", sz, p - (char*)resp);
 ret:
	return resp;
}

typedef struct gr_response_header {
	uint32_t version_or_size;
	int32_t found;
	int32_t gr_name_len;    /* strlen(gr->gr_name) + 1; */
	int32_t gr_passwd_len;  /* strlen(gr->gr_passwd) + 1; */
	int32_t gr_gid;         /* gr->gr_gid */
	int32_t gr_mem_cnt;     /* while (gr->gr_mem[gr_mem_cnt]) ++gr_mem_cnt; */
	/* int32_t gr_mem_len[gr_mem_cnt]; */
	/* char gr_name[gr_name_len]; */
	/* char gr_passwd[gr_passwd_len]; */
	/* char gr_mem[gr_mem_cnt][gr_mem_len[i]]; */
	/* char gr_gid_str[as_needed]; - huh? */
	/* char orig_key[as_needed]; - needed?? I don't do this ATM... */
/*
 glibc adds gr_gid_str, but client doesn't get/use it:
 writev(3, [{"\2\0\0\0\2\0\0\0\5\0\0\0", 12}, {"root\0", 5}], 2) = 17
 poll([{fd=3, events=POLLIN|POLLERR|POLLHUP, revents=POLLIN}], 1, 5000) = 1
 read(3, "\2\0\0\0\1\0\0\0\10\0\0\0\4\0\0\0\0\0\0\0\0\0\0\0", 24) = 24
 readv(3, [{"", 0}, {"root\0\0\0\0\0\0\0\0", 12}], 2) = 12
 read(3, NULL, 0)        = 0
*/
} gr_response_header;

static gr_response_header *marshal_group(struct group *gr)
{
	char *p;
	gr_response_header *resp;
	unsigned gr_mem_cnt;
	unsigned sz = sizeof(*resp);
	if (gr) {
		sz += strsize(gr->gr_name);
		sz += strsize(gr->gr_passwd);
		gr_mem_cnt = 0;
		while (gr->gr_mem[gr_mem_cnt]) {
			sz += strsize(gr->gr_mem[gr_mem_cnt]);
			gr_mem_cnt++;
		}
		/* for int32_t gr_mem_len[gr_mem_cnt]; */
		sz += gr_mem_cnt * sizeof(int32_t);
	}
	resp = xzalloc(sz);
	resp->version_or_size = sz;
	if (!gr) {
		/*resp->found = 0;*/
		goto ret;
	}
	resp->found = 1;
	resp->gr_name_len = strsize(gr->gr_name);
	resp->gr_passwd_len = strsize(gr->gr_passwd);
	resp->gr_gid = gr->gr_gid;
	resp->gr_mem_cnt = gr_mem_cnt;
	p = (char*)(resp + 1);
/* int32_t gr_mem_len[gr_mem_cnt]; */
	gr_mem_cnt = 0;
	while (gr->gr_mem[gr_mem_cnt]) {
		*(uint32_t*)p = strsize(gr->gr_mem[gr_mem_cnt]);
		p += 4;
		gr_mem_cnt++;
	}
/* char gr_name[gr_name_len]; */
	strcpy(p, gr->gr_name);
	p += strsize(gr->gr_name);
/* char gr_passwd[gr_passwd_len]; */
	strcpy(p, gr->gr_passwd);
	p += strsize(gr->gr_passwd);
/* char gr_mem[gr_mem_cnt][gr_mem_len[i]]; */
	gr_mem_cnt = 0;
	while (gr->gr_mem[gr_mem_cnt]) {
		strcpy(p, gr->gr_mem[gr_mem_cnt]);
		p += strsize(gr->gr_mem[gr_mem_cnt]);
		gr_mem_cnt++;
	}
	log(L_DEBUG, "sz:%u realsz:%u", sz, p - (char*)resp);
 ret:
	return resp;
}

typedef struct hst_response_header {
	uint32_t version_or_size;
	int32_t found;
	int32_t h_name_len;
	int32_t h_aliases_cnt;
	int32_t h_addrtype;     /* AF_INET or AF_INET6 */
	int32_t h_length;       /* 4 or 16 */
	int32_t h_addr_list_cnt;
	int32_t error;
	/* char h_name[h_name_len]; - we pad it to 4 bytes */
	/* uint32_t h_aliases_len[h_aliases_cnt]; */
	/* char h_addr_list[h_addr_list_cnt][h_length]; - every one is the same size [h_length] (4 or 16) */
	/* char h_aliases[h_aliases_cnt][h_aliases_len[i]]; */
} hst_response_header;

static hst_response_header *marshal_hostent(struct hostent *h)
{
	char *p;
	hst_response_header *resp;
	unsigned h_name_len;
	unsigned h_aliases_cnt;
	unsigned h_addr_list_cnt;
	unsigned sz = sizeof(*resp);
	if (h) {
/* char h_name[h_name_len] */
		sz += h_name_len = strsize_aligned4(h->h_name);
		h_addr_list_cnt = 0;
		while (h->h_addr_list[h_addr_list_cnt]) {
			h_addr_list_cnt++;
		}
/* char h_addr_list[h_addr_list_cnt][h_length] */
		sz += h_addr_list_cnt * h->h_length;
		h_aliases_cnt = 0;
		while (h->h_aliases[h_aliases_cnt]) {
/* char h_aliases[h_aliases_cnt][h_aliases_len[i]] */
			sz += strsize(h->h_aliases[h_aliases_cnt]);
			h_aliases_cnt++;
		}
/* uint32_t h_aliases_len[h_aliases_cnt] */
		sz += h_aliases_cnt * 4;
	}
	resp = xzalloc(sz);
	resp->version_or_size = sz;
	if (!h) {
		/*resp->found = 0;*/
		resp->error = HOST_NOT_FOUND;
		goto ret;
	}
	resp->found = 1;
	resp->h_name_len = h_name_len;
	resp->h_aliases_cnt = h_aliases_cnt;
	resp->h_addrtype = h->h_addrtype;
	resp->h_length = h->h_length;
	resp->h_addr_list_cnt = h_addr_list_cnt;
	/*resp->error = 0;*/
	p = (char*)(resp + 1);
/* char h_name[h_name_len]; */
	strcpy(p, h->h_name);
	p += h_name_len;
/* uint32_t h_aliases_len[h_aliases_cnt]; */
	h_aliases_cnt = 0;
	while (h->h_aliases[h_aliases_cnt]) {
		*(uint32_t*)p = strsize(h->h_aliases[h_aliases_cnt]);
		p += 4;
		h_aliases_cnt++;
	}
/* char h_addr_list[h_addr_list_cnt][h_length]; */
	h_addr_list_cnt = 0;
	while (h->h_addr_list[h_addr_list_cnt]) {
		memcpy(p, h->h_addr_list[h_addr_list_cnt], h->h_length);
		p += h->h_length;
		h_addr_list_cnt++;
	}
/* char h_aliases[h_aliases_cnt][h_aliases_len[i]]; */
	h_aliases_cnt = 0;
	while (h->h_aliases[h_aliases_cnt]) {
		strcpy(p, h->h_aliases[h_aliases_cnt]);
		p += strsize(h->h_aliases[h_aliases_cnt]);
		h_aliases_cnt++;
	}
	log(L_DEBUG, "sz:%u realsz:%u", sz, p - (char*)resp);
 ret:
	return resp;
}

/* Reply to addrinfo query */
typedef struct ai_response_header {
	uint32_t version_or_size;
	int32_t found;
	int32_t naddrs;
	int32_t addrslen;
	int32_t canonlen;
	int32_t error;
	/* char ai_addr[naddrs][4 or 16]; - addrslen bytes in total */
	/* char ai_family[naddrs]; - AF_INET[6] each (determines ai_addr[i] length) */
	/* char ai_canonname[canonlen]; */
} ai_response_header;

static ai_response_header *obtain_addrinfo(const char *hostname)
{
	struct addrinfo hints;
	struct addrinfo *ai;
	struct addrinfo *ap;
	ai_response_header *resp;
	char *p, *family;
	int err;
	unsigned sz;
	unsigned naddrs = 0;
	unsigned addrslen = 0;
	unsigned canonlen = 0;

	memset(&hints, 0, sizeof(hints));
	hints.ai_flags = AI_CANONNAME;
	/* kills dups (one for each possible SOCK_xxx) */
	/* this matches glibc behavior */
	hints.ai_socktype = SOCK_STREAM;
	ai = NULL; /* on failure getaddrinfo may leave it as-is */
	err = getaddrinfo(hostname, NULL, &hints, &ai);

	sz = sizeof(*resp);
	if (!err) {
		if (ai->ai_canonname)
			sz += canonlen = strsize(ai->ai_canonname);
		ap = ai;
		do {
			naddrs++;
			addrslen += (ap->ai_family == AF_INET ? 4 : 16);
			ap = ap->ai_next;
		} while (ap);
		sz += naddrs + addrslen;
	}
	resp = xzalloc(sz);
	resp->version_or_size = sz;
	resp->error = err;
	if (err) {
		/*resp->found = 0;*/
		goto ret;
	}
	resp->found = 1;
	resp->naddrs = naddrs;
	resp->addrslen = addrslen;
	resp->canonlen = canonlen;
	p = (char*)(resp + 1);
	family = p + addrslen;
	ap = ai;
	do {
/* char ai_family[naddrs]; */
		*family++ = ap->ai_family;
/* char ai_addr[naddrs][4 or 16]; */
		if (ap->ai_family == AF_INET) {
			memcpy(p, &(((struct sockaddr_in*)(ap->ai_addr))->sin_addr), 4);
			p += 4;
		} else {
			memcpy(p, &(((struct sockaddr_in6*)(ap->ai_addr))->sin6_addr), 16);
			p += 16;
		}
		ap = ap->ai_next;
	} while (ap);
/* char ai_canonname[canonlen]; */
	if (ai->ai_canonname)
		strcpy(family, ai->ai_canonname);
	log(L_DEBUG, "sz:%u realsz:%u", sz, family + strsize(ai->ai_canonname) - (char*)resp);
 ret:
	/* glibc 2.3.6 segfaults here sometimes
	 * (maybe my mistake, fixed by "ai = NULL;" above).
	 * Since we are in worker and are going to exit anyway, why bother? */
	/*freeaddrinfo(ai);*/
	return resp;
}


/*
** Cache management
*/

/* one 8-element "cacheline" */
typedef user_req *cacheline_t[8];
static unsigned cache_size;
/* Points to cacheline_t  cache[cache_size] array, or in other words,
 * points to user_req*    cache[cache_size][8] array */
static cacheline_t *cache;
static unsigned cached_cnt;
static unsigned cache_access_cnt = 1; /* prevent division by zero */
static unsigned cache_hit_cnt = 1;
static unsigned last_age_time;
static unsigned aging_interval_ms;
static unsigned min_aging_interval_ms;

static response_header *ureq_response(user_req *ureq)
{
	/* Skip query part, find answer part
	 * (answer is 32-bit aligned) */
	return (void*) ((char*)ureq + ((ureq_size(ureq) + 3) & ~3));
}

/* This hash is supposed to be good for short textual data */
static uint32_t bernstein_hash(void *p, unsigned sz, uint32_t hash)
{
	uint8_t *key = p;
	do {
		hash = (32 * hash + hash) ^ *key++;
	} while (--sz);
	return hash;
}

static void free_refcounted_ureq(user_req **ureqp)
{
	user_req *ureq = *ureqp;

	if (!CACHED_ENTRY(ureq))
		return;

	if (ureq->refcount) {
		ureq->refcount--;
	} else {
		log(L_DEBUG2, "refcount == 0, free(%p)", ureq);
		free(ureq);
	}
	*ureqp = NULL;
}

static user_req **lookup_in_cache(user_req *ureq)
{
	user_req **cacheline;
	int free_cache;
	unsigned hash;
	unsigned i;
	unsigned ureq_sz = ureq_size(ureq);

	/* prevent overflow and division by zero */
	cache_access_cnt++;
	if ((int)cache_access_cnt < 0) {
		cache_access_cnt = (cache_access_cnt >> 1) + 1;
		cache_hit_cnt = (cache_hit_cnt >> 1) + 1;
	}

	hash = bernstein_hash(&ureq->key_len, ureq_sz - offsetof(user_req, key_len), ureq->type);
	log(L_DEBUG2, "hash:%08x", hash);
	hash = hash % cache_size;
	cacheline = cache[hash];

	free_cache = -1;
	for (i = 0; i < 8; i++) {
		user_req *cached = CACHE_PTR(cacheline[i]);
		if (!cached) {
			if (free_cache == -1)
				free_cache = i;
			continue;
		}
		/* ureq->version is always 2 and is reused in cache
		 * for other purposes, we need to skip it here */
		if (memcmp(&ureq->type, &cached->type, ureq_sz - offsetof(user_req, type)) == 0) {
			log(L_DEBUG, "found in cache[%u][%u]", hash, i);
			cache_hit_cnt++;
			return &cacheline[i];
		}
	}

	if (free_cache >= 0) {
		cached_cnt++;
		i = free_cache;
		log(L_DEBUG, "not found, using free cache[%u][%u]", hash, i);
		goto ret;
	}

	unsigned oldest_idx = 0;
	unsigned oldest_age = 0;
	for (i = 0; i < 8; i++) {
		unsigned age = cache_age(cacheline[i]);
		if (age > oldest_age) {
			oldest_age = age;
			oldest_idx = i;
		}
	}
	if (oldest_age == 0) {
		/* All entries in cacheline are "future" entries!
		 * This is very unlikely, but we must still work correctly.
		 * We call this "fake cache entry".
		 * The data will be "cached" only for the duration
		 * of this client's request lifetime.
		 */
		log(L_DEBUG, "not found, and cache[%u] is full: using fake cache entry", hash);
		return NULL;
	}
	i = oldest_idx;
	log(L_DEBUG, "not found, freeing and reusing cache[%u][%u] (age %u)", hash, i, oldest_age);
	free_refcounted_ureq(&cacheline[i]);

 ret:
	cacheline[i] = MAKE_FUTURE_PTR(ureq);
	return &cacheline[i];
}

static void age_cache(unsigned free_all, int srv)
{
	user_req **cp = *cache;
	int i;
	unsigned sv = cached_cnt;

	log(L_DEBUG, "aging cache, srv:%d, free_all:%u", srv, free_all);
	if (srv == -1 || free_all)
		aging_interval_ms = INT_MAX;
	i = cache_size * 8;
	do {
		user_req *cached = *cp;
		if (CACHED_ENTRY(cached) && cached != NULL) {
			int csrv = type_to_srv[cached->type];
			if (srv == -1 || srv == csrv) {
				if (free_all) {
					cached_cnt--;
					free_refcounted_ureq(cp);
				} else {
                        		unsigned age = cache_age(cached);
					response_header *resp = ureq_response(cached);
					unsigned ttl = (resp->found ? config.pttl : config.nttl)[csrv];
					if (age >= ttl) {
						log(L_DEBUG2, "freeing: age %u positive %d ttl %u", age, resp->found, ttl);
						cached_cnt--;
						free_refcounted_ureq(cp);
					} else if (srv == -1) {
						ttl -= age;
						if (aging_interval_ms > ttl)
							aging_interval_ms = ttl;
					}
				}
			}
		}
		cp++;
	} while (--i);
	log(L_INFO, "aged cache, freed:%u, remain:%u", sv - cached_cnt, cached_cnt);
	log(L_DEBUG2, "aging interval now %u ms", aging_interval_ms);
}


/*
** Worker child
*/

/* Spawns a worker and feeds it with user query on stdin */
/* Returns stdout fd of the worker, in blocking mode */
static int create_and_feed_worker(user_req *ureq)
{
	pid_t pid;
	struct {
		int rd;
		int wr;
	} to_child, to_parent;

	/* NB: these pipe fds are in blocking mode and non-CLOEXECed */
	xpipe(&to_child.rd);
	xpipe(&to_parent.rd);

	pid = vfork();
	if (pid < 0) /* error */
		perror_and_die("vfork");
	if (!pid) { /* child */
		char param[sizeof(int)*3 + 2];
		char *argv[3];

		close(to_child.wr);
		close(to_parent.rd);
		xmovefd(to_child.rd, 0);
		xmovefd(to_parent.wr, 1);
		sprintf(param, "%u", debug);
		argv[0] = (char*) "worker_nscd";
		argv[1] = param;
		argv[2] = NULL;
		/* Re-exec ourself, cleaning up all allocated memory.
		 * fds in parent are marked CLOEXEC and will be closed too
		 * (modulo bugs) */
		/* Try link name first: it's better to have comm field
		 * of "nscd" than "exe" (pgrep reported to fail to find us
		 * by name when comm field contains "exe") */
		execve(self_exe_points_to, argv, argv+2);
		xexecve("/proc/self/exe", argv, argv+2);
	}

	/* parent */
	close(to_child.rd);
	close(to_parent.wr);
	/* We do not expect child to block for any noticeably long time,
	 * and also we expect write to be one-piece one:
	 * ureq size is <= 1k and pipes are guaranteed to accept
	 * at least PIPE_BUF at once */
	xsafe_write(to_child.wr, ureq, ureq_size(ureq));

	close(to_child.wr);
	close_on_exec(to_parent.rd);
	return to_parent.rd;
}

static user_req *worker_ureq;

#if DEBUG_BUILD
static const char *req_str(unsigned type, const char *buf)
{
	if (type == GETHOSTBYADDR) {
		struct in_addr in;
		in.s_addr = *((uint32_t*)buf);
		return inet_ntoa(in);
	}
	if (type == GETHOSTBYADDRv6) {
		return "IPv6";
	}
	return buf;
}
#else
const char *req_str(unsigned type, const char *buf);
#endif

static void worker_signal_handler(int sig)
{
#if DEBUG_BUILD
	log(L_INFO, "worker:%d got sig:%d while handling req "
		"type:%d(%s) key_len:%d '%s'",
		getpid(), sig,
		worker_ureq->type, typestr[worker_ureq->type],
		worker_ureq->key_len,
		req_str(worker_ureq->type, worker_ureq->reqbuf)
	);
#else
	log(L_INFO, "worker:%d got sig:%d while handling req "
		"type:%d key_len:%d",
		getpid(), sig,
		worker_ureq->type, worker_ureq->key_len);
#endif
	_exit(0);
}

static void worker(const char *param) NORETURN;
static void worker(const char *param)
{
	user_req ureq;
	void *resp;

	debug = atoi(param);

	worker_ureq = &ureq; /* for signal handler */

	/* Make sure we won't hang, but rather die */
	if (WORKER_TIMEOUT_SEC)
		alarm(WORKER_TIMEOUT_SEC);

	/* NB: fds 0, 1 are in blocking mode */

	/* We block here (for a short time) */
	/* Due to ureq size < PIPE_BUF read is atomic */
	/* No error or size checking: we trust the parent */
	safe_read(0, &ureq, sizeof(ureq));

	signal(SIGSEGV,   worker_signal_handler);
	signal(SIGBUS,    worker_signal_handler);
	signal(SIGILL,    worker_signal_handler);
	signal(SIGFPE,    worker_signal_handler);
	signal(SIGABRT,   worker_signal_handler);
#ifdef SIGSTKFLT
	signal(SIGSTKFLT, worker_signal_handler);
#endif

	if (ureq.type == GETHOSTBYNAME
	 || ureq.type == GETHOSTBYNAMEv6
	) {
		resp = marshal_hostent(
			ureq.type == GETHOSTBYNAME
			? gethostbyname(ureq.reqbuf)
			: gethostbyname2(ureq.reqbuf, AF_INET6)
		);
	} else if (ureq.type == GETHOSTBYADDR
	 || ureq.type == GETHOSTBYADDRv6
	) {
		resp = marshal_hostent(gethostbyaddr(ureq.reqbuf, ureq.key_len,
			(ureq.type == GETHOSTBYADDR ? AF_INET : AF_INET6)
		));
	} else if (ureq.type == GETPWBYNAME) {
		struct passwd *pw;
		log(L_DEBUG2, "getpwnam('%s')", ureq.reqbuf);
		pw = getpwnam(ureq.reqbuf);
		log(L_DEBUG2, "getpwnam result:%p", pw);
		resp = marshal_passwd(pw);
	} else if (ureq.type == GETPWBYUID) {
		resp = marshal_passwd(getpwuid(atoi(ureq.reqbuf)));
	} else if (ureq.type == GETGRBYNAME) {
		struct group *gr = getgrnam(ureq.reqbuf);
		resp = marshal_group(gr);
	} else if (ureq.type == GETGRBYGID) {
		struct group *gr = getgrgid(atoi(ureq.reqbuf));
		resp = marshal_group(gr);
	} else if (ureq.type == GETAI) {
		resp = obtain_addrinfo(ureq.reqbuf);
	} else /*if (ureq.type == INITGROUPS)*/ {
		resp = obtain_initgroups(ureq.reqbuf);
	}

	if (!((response_header*)resp)->found) {
		/* Parent knows about this special case */
		xfull_write(1, resp, 8);
	} else {
		/* Responses can be big (getgrnam("guest") on a big user db),
		 * we cannot rely on them being atomic. full_write loops
		 * if needed */
		xfull_write(1, resp, ((response_header*)resp)->version_or_size);
	}
	_exit(0);
}


/*
** Main loop
*/

static const char checked_filenames[][sizeof("/etc/passwd")] = {
	[SRV_PASSWD] = "/etc/passwd", /*  "/etc/shadow"? */
	[SRV_GROUP]  = "/etc/group",
	[SRV_HOSTS]  = "/etc/hosts", /* "/etc/resolv.conf" "/etc/nsswitch.conf"? */
};

static long checked_status[ARRAY_SIZE(checked_filenames)];

static void check_files(int srv)
{
	struct stat tsb;
	const char *file = checked_filenames[srv];
	long v;

	memset(&tsb, 0, sizeof(tsb));
	stat(file, &tsb); /* ignore errors */
	/* Comparing struct stat's was giving false positives.
	 * Extracting only those fields which are interesting: */
	v = (long)tsb.st_mtime ^ (long)tsb.st_size ^ (long)tsb.st_ino; /* ^ (long)tsb.st_dev ? */

	if (v != checked_status[srv]) {
		checked_status[srv] = v;
		log(L_INFO, "detected change in %s", file);
		age_cache(/*free_all:*/ 1, srv);
	}
}

/* Returns 1 if we immediately have the answer */
static int handle_client(int i)
{
	int srv;
	user_req *ureq = cinfo[i].ureq;
	user_req **cache_pp;
	user_req *ureq_and_resp;

#if DEBUG_BUILD
	log(L_DEBUG, "version:%d type:%d(%s) key_len:%d '%s'",
			ureq->version, ureq->type,
			ureq->type < ARRAY_SIZE(typestr) ? typestr[ureq->type] : "BAD",
			ureq->key_len, req_str(ureq->type, ureq->reqbuf));
#endif

	if (ureq->version != NSCD_VERSION) {
		log(L_INFO, "wrong version");
		close_client(i);
		return 0;
	}
	if (ureq->key_len > sizeof(ureq->reqbuf)) {
		log(L_INFO, "bogus key_len %u - ignoring", ureq->key_len);
		close_client(i);
		return 0;
	}
	if (cinfo[i].bytecnt < USER_HDR_SIZE + ureq->key_len) {
		log(L_INFO, "read %d, need to read %d",
			cinfo[i].bytecnt, USER_HDR_SIZE + ureq->key_len);
		return 0; /* more to read */
	}
	if (cinfo[i].bytecnt > USER_HDR_SIZE + ureq->key_len) {
		log(L_INFO, "read overflow");
		close_client(i);
		return 0;
	}
	if (unsupported_ureq_type(ureq->type)) {
		/* We don't know this request. Just close the connection.
		 * (glibc client interprets this like "not supported by this nscd")
		 * Happens very often, thus DEBUG, not INFO */
		log(L_DEBUG, "unsupported query, dropping");
		close_client(i);
		return 0;
	}
	srv = type_to_srv[ureq->type];
	if (!config.srv_enable[srv]) {
		log(L_INFO, "service %d is disabled, dropping", srv);
		close_client(i);
		return 0;
	}

	hex_dump(cinfo[i].ureq, cinfo[i].bytecnt);

	if (ureq->type == SHUTDOWN
	 || ureq->type == INVALIDATE
	) {
#ifdef SO_PEERCRED
		struct ucred caller;
		socklen_t optlen = sizeof(caller);
		if (getsockopt(pfd[i].fd, SOL_SOCKET, SO_PEERCRED, &caller, &optlen) < 0) {
			log(L_INFO, "ignoring special request - cannot get caller's id: %s", strerror(errno));
			close_client(i);
			return 0;
		}
		if (caller.uid != 0) {
			log(L_INFO, "special request from non-root - ignoring");
			close_client(i);
			return 0;
		}
#endif
		if (ureq->type == SHUTDOWN) {
			log(L_INFO, "got shutdown request, exiting");
			exit(0);
		}
		if (!ureq->key_len || ureq->reqbuf[ureq->key_len - 1]) {
			log(L_INFO, "malformed invalidate request - ignoring");
			close_client(i);
			return 0;
		}
		log(L_INFO, "got invalidate request, flushing cache");
		/* Frees entire cache. TODO: replace -1 with service (in ureq->reqbuf) */
		age_cache(/*free_all:*/ 1, -1);
		close_client(i);
		return 0;
	}

	if (ureq->type != GETHOSTBYADDR
	 && ureq->type != GETHOSTBYADDRv6
	) {
		if (ureq->key_len && ureq->reqbuf[ureq->key_len - 1] != '\0') {
			log(L_INFO, "badly terminated buffer");
			close_client(i);
			return 0;
		}
	}

	if (config.check_files[srv]) {
		check_files(srv);
	}

	cache_pp = lookup_in_cache(ureq);
	ureq_and_resp = cache_pp ? *cache_pp : NULL;

	if (ureq_and_resp) {
		if (CACHED_ENTRY(ureq_and_resp)) {
			/* Found. Save ptr to response into cinfo and return */
			response_header *resp = ureq_response(ureq_and_resp);
			unsigned sz = resp->version_or_size;

			log(L_DEBUG, "sz:%u", sz);
			hex_dump(resp, sz);
			ureq_and_resp->refcount++; /* cache shouldn't free it under us! */
			pfd[i].events = POLLOUT; /* we want to write out */
			cinfo[i].resptr = ureq_and_resp;
			/*cinfo[i].respos = 0; - already is */
			/* prevent future matches with anything */
			cinfo[i].cache_pp = (void *) 1;
			return 1; /* "ready to write data out to client" */
		}

		/* Not found. Remember a pointer where it will appear */
		cinfo[i].cache_pp = cache_pp;

		/* If it does not point to our own ureq buffer... */
		if (CACHE_PTR(ureq_and_resp) != ureq) {
			/* We are not the first client who wants this */
			log(L_DEBUG, "another request is in progress (%p), waiting for its result", ureq_and_resp);
			MARK_PTR_SHARED(cache_pp); /* "please inform us when it's ready" */
			/* "we do not wait for client anymore" */
			cinfo[i].client_fd = pfd[i].fd;
			/* Don't wait on fd. Worker response will unblock us */
			pfd[i].events = 0;
			return 0;
		}
		/* else: lookup_in_cache inserted (ureq & 1) into *cache_pp:
		 * we are the first client to miss on this ureq. */
	}

	/* Start worker thread */
	log(L_DEBUG, "stored %p in cache, starting a worker", ureq_and_resp);
	/* Now we will wait on worker's fd, not client's! */
	cinfo[i].client_fd = pfd[i].fd;
	pfd[i].fd = create_and_feed_worker(ureq);
	return 0;
}

static void prepare_for_writeout(unsigned i, user_req *cached)
{
	log(L_DEBUG2, "client %u: data is ready at %p", i, cached);

	if (cinfo[i].client_fd) {
		pfd[i].fd = cinfo[i].client_fd;
		cinfo[i].client_fd = 0; /* "we don't wait for worker reply" */
	}
	pfd[i].events = POLLOUT;

	/* Writeout position etc */
	cinfo[i].resptr = cached;
	/*cinfo[i].respos = 0; - already is */
	/* if worker took some time to get info (e.g. DNS query),
	 * prevent client timeout from triggering at once */
	cinfo[i].started_ms = g_now_ms;
}

/* Worker seems to be ready to write the response.
 * When we return, response is fully read and stored in cache,
 * worker's fd is closed, pfd[i] and cinfo[i] are updated. */
static void handle_worker_response(int i)
{
	struct { /* struct response_header + small body */
		uint32_t version_or_size;
		int32_t found;
		char body[256 - 8];
	} sz_and_found;
	user_req *cached;
	user_req *ureq;
	response_header *resp;
	unsigned sz, resp_sz;
	unsigned ureq_sz_aligned;

	cached = NULL;
	ureq = cinfo[i].ureq;
	ureq_sz_aligned = (char*)ureq_response(ureq) - (char*)ureq;

	sz = full_read(pfd[i].fd, &sz_and_found, sizeof(sz_and_found));
	if (sz < 8) {
		/* worker was killed? */
		log(L_DEBUG, "worker gave short reply:%u < 8", sz);
		goto err;
	}

	resp_sz = sz_and_found.version_or_size;
	if (resp_sz < sz || resp_sz > 0xfffffff) { /* 256 mb */
		error("BUG: bad size from worker:%u", resp_sz);
		goto err;
	}

	/* Create new block of cached info */
	cached = xzalloc(ureq_sz_aligned + resp_sz);
	log(L_DEBUG2, "xzalloc(%u):%p", ureq_sz_aligned + resp_sz, cached);
	resp = (void*) (((char*) cached) + ureq_sz_aligned);
	memcpy(cached, ureq, ureq_size(ureq));
	memcpy(resp, &sz_and_found, sz);
	if (sz_and_found.found && resp_sz > sz) {
		/* We need to read data only if it's found
		 * (otherwise worker sends only 8 bytes).
		 *
		 * Replies can be big (getgrnam("guest") on a big user db),
		 * we cannot rely on them being atomic. However, we know
		 * that worker _always_ gives reply in one full_write(),
		 * so we loop and read it all
		 * (looping is implemented inside full_read())
		 */
		if (full_read(pfd[i].fd, ((char*) resp) + sz, resp_sz - sz) != resp_sz - sz) {
			/* worker was killed? */
			log(L_DEBUG, "worker gave short reply, free(%p)", cached);
 err:
			free(cached);
			cached = NULL;
			goto wo;
		}
	}
	set_cache_timestamp(cached);
	hex_dump(resp, resp_sz);

 wo:
	close(pfd[i].fd);

	/* Save in cache */
	unsigned ref = 0;
	user_req **cache_pp = cinfo[i].cache_pp;
	if (cache_pp != NULL) { /* if not a fake entry */
		ureq = *cache_pp;
		*cache_pp = cached;
		if (CACHE_SHARED(ureq)) {
			/* Other clients wait for this response too,
			 * wake them (and us) up and set refcount = no_of_clients */
			unsigned j;

			for (j = 2; j < num_clients; j++) {
				if (cinfo[j].cache_pp == cache_pp) {
					/* This client uses the same cache entry */
					ref++;
					/* prevent future matches with anything */
					cinfo[j].cache_pp = (void *) 1;
					prepare_for_writeout(j, cached);
				}
			}
			goto ret;
		}
		/* prevent future matches with anything */
		cinfo[i].cache_pp = (void *) 1;
		ref = 1;
	}

	prepare_for_writeout(i, cached);
ret:
	/* cache shouldn't free it under us! */
	if (cached)
		cached->refcount = ref;
	aging_interval_ms = min_aging_interval_ms;
}

static void main_loop(void)
{
	/* 1/2 of smallest negative TTL */
	min_aging_interval_ms = config.nttl[0];
	if (min_aging_interval_ms > config.nttl[1]) min_aging_interval_ms = config.nttl[1];
	if (min_aging_interval_ms > config.nttl[2]) min_aging_interval_ms = config.nttl[2];
	min_aging_interval_ms = (min_aging_interval_ms / 2) | 1;
	aging_interval_ms = min_aging_interval_ms;

	while (1) {
		int i, j;
		int r;

		r = SMALL_POLL_TIMEOUT_MS;
		if (num_clients <= 2 && !cached_cnt)
			r = -1; /* infinite */
		else if (num_clients < max_reqnum)
			r = aging_interval_ms;
#if 0 /* Debug: leak detector */
		{
			static unsigned long long cnt;
			static unsigned long low_malloc = -1L;
			static unsigned long low_sbrk = -1L;
			void *p = malloc(540); /* should not be too small */
			void *s = sbrk(0);
			free(p);
			if ((unsigned long)p < low_malloc)
				low_malloc = (unsigned long)p;
			if ((unsigned long)s < low_sbrk)
				low_sbrk = (unsigned long)s;
			log(L_INFO, "poll %llu (%d ms). clients:%u cached:%u %u/%u malloc:%p (%lu), sbrk:%p (%lu)",
				cnt, r, num_clients, cached_cnt, cache_hit_cnt, cache_access_cnt,
				p, (unsigned long)p - low_malloc,
				s, (unsigned long)s - low_sbrk);
			cnt++;
		}
#else
		log(L_DEBUG, "poll %d ms. clients:%u cached:%u hit ratio:%u/%u",
				r, num_clients, cached_cnt, cache_hit_cnt, cache_access_cnt);
#endif

		r = poll(pfd, num_clients, r);
		log(L_DEBUG2, "poll returns %d", r);
		if (r < 0) {
			if (errno != EINTR)
				perror_and_die("poll");
			continue;
		}

		/* Everything between polls never sleeps.
		 * There is no blocking I/O (except when we talk to worker thread
		 * which is guaranteed to not block us for long) */

		g_now_ms = monotonic_ms();
		if (r == 0)
			goto skip_fd_checks;

		for (i = 0; i < 2; i++) {
			int cfd;
			if (!pfd[i].revents)
				continue;
			/* pfd[i].revents = 0; - not needed */
			cfd = accept(pfd[i].fd, NULL, NULL);
			if (cfd < 0) {
				/* odd... poll() says we can accept but accept failed? */
				log(L_DEBUG2, "accept failed with %s", strerror(errno));
				continue;
			}
			ndelay_on(cfd);
			close_on_exec(cfd);
			/* x[num_clients] is next free element, taking it */
			log(L_DEBUG2, "new client %d, fd %d", num_clients, cfd);
			pfd[num_clients].fd = cfd;
			pfd[num_clients].events = POLLIN;
			/* this will make us do read() in next for() loop: */
			pfd[num_clients].revents = POLLIN;
			memset(&cinfo[num_clients], 0, sizeof(cinfo[num_clients]));
			/* cinfo[num_clients].bytecnt = 0; - done */
			cinfo[num_clients].started_ms = g_now_ms;
			cinfo[num_clients].bufidx = alloc_buf_no();
			cinfo[num_clients].ureq = bufno2buf(cinfo[num_clients].bufidx);
			num_clients++;
			if (num_clients >= max_reqnum) {
				/* stop accepting new connects for now */
				pfd[0].events = pfd[0].revents = 0;
				pfd[1].events = pfd[1].revents = 0;
			}
		}
		for (; i < num_clients; i++) {
			if (!pfd[i].revents)
				continue;
			log(L_DEBUG2, "pfd[%d].revents:0x%x", i, pfd[i].revents);
			/* pfd[i].revents = 0; - not needed */

			/* "Write out result" case */
			if (pfd[i].revents == POLLOUT) {
				response_header *resp;
				uint32_t resp_sz;
				if (!cinfo[i].resptr) {
					/* corner case: worker gave bad response earlier */
					close_client(i);
					continue;
				}
 write_out:
				resp = ureq_response(cinfo[i].resptr);
				resp_sz = resp->version_or_size;
				resp->version_or_size = NSCD_VERSION;
				r = safe_write(pfd[i].fd, ((char*) resp) + cinfo[i].respos, resp_sz - cinfo[i].respos);
				resp->version_or_size = resp_sz;

				if (r < 0 && errno == EAGAIN)
					continue;
				if (r <= 0) { /* client isn't there anymore */
					log(L_DEBUG, "client %d is gone (write returned %d)", i, r);
 write_out_is_done:
					if (cinfo[i].cache_pp == NULL) {
						log(L_DEBUG, "client %d: freeing fake cache entry %p", i, cinfo[i].resptr);
						free(cinfo[i].resptr);
					} else {
						/* Most of the time, it is not freed here,
						 * only refcounted--. Freeing happens
						 * if it was deleted from cache[] but retained
						 * for writeout. */
						free_refcounted_ureq(&cinfo[i].resptr);
					}
					close_client(i);
					continue;
				}
				cinfo[i].respos += r;
				if (cinfo[i].respos >= resp_sz) {
					/* We wrote everything */
					/* No point in trying to get next request, it won't come.
					 * glibc 2.4 client closes its end after each request,
					 * without testing for EOF from server. strace:
					 * ...
					 * read(3, "www.google.com\0\0", 16) = 16
					 * close(3) = 0
					 */
					log(L_DEBUG, "client %u: sent answer %u bytes", i, cinfo[i].respos);
					goto write_out_is_done;
				}
			}

			/* "Read reply from worker" case. Worker may be
			 * already dead, revents may contain other bits too */
			if ((pfd[i].revents & POLLIN) && cinfo[i].client_fd) {
				log(L_DEBUG, "reading response for client %u", i);
				handle_worker_response(i);
				/* We can immediately try to write a response
				 * to client */
				goto write_out;
			}

			/* POLLHUP means pfd[i].fd is closed by peer.
			 * POLLHUP+POLLOUT is seen when we switch for writeout
			 * and see that pfd[i].fd is closed by peer. */
			if ((pfd[i].revents & ~POLLOUT) == POLLHUP) {
				int is_client = (cinfo[i].client_fd == 0 || cinfo[i].client_fd == pfd[i].fd);
				log(L_INFO, "%s %u disappeared (got POLLHUP on fd %d)",
					is_client ? "client" : "worker",
					i,
					pfd[i].fd
				);
				if (is_client)
					close_client(i);
				else {
					/* Read worker output anyway, error handling
					 * in that function deals with short read.
					 * Simply closing client is wrong: it leaks
					 * shared future entries. */
					handle_worker_response(i);
				}
				continue;
			}

			/* All strange and unexpected cases */
			if (pfd[i].revents != POLLIN) {
				/* Not just "can read", but some other bits are there */
				log(L_INFO, "client %u revents is strange:%x", i, pfd[i].revents);
				close_client(i);
				continue;
			}

			/* "Read request from client" case */
			r = safe_read(pfd[i].fd, (char*)(cinfo[i].ureq) + cinfo[i].bytecnt, MAX_USER_REQ_SIZE - cinfo[i].bytecnt);
			if (r < 0) {
				log(L_DEBUG2, "error reading from client: %s", strerror(errno));
				if (errno == EAGAIN)
					continue;
				close_client(i);
				continue;
			}
			if (r == 0) {
				log(L_INFO, "premature EOF from client, dropping");
				close_client(i);
				continue;
			}
			cinfo[i].bytecnt += r;
			if (cinfo[i].bytecnt >= sizeof(user_req_header)) {
				if (handle_client(i)) {
					/* Response is found in cache! */
					goto write_out;
				}
			}
		} /* for each client[2..num_clients-1] */

 skip_fd_checks:
		/* Age cache */
		if ((g_now_ms - last_age_time) >= aging_interval_ms) {
			last_age_time = g_now_ms;
			age_cache(/*free_all:*/ 0, -1);
		}

		/* Close timed out client connections */
		for (i = 2; i < num_clients; i++) {
			if (pfd[i].fd != 0 /* not closed yet? */ ////
			 && cinfo[i].client_fd == 0 /* do we still wait for client, not worker? */
			 && (g_now_ms - cinfo[i].started_ms) > CLIENT_TIMEOUT_MS
			) {
				log(L_INFO, "timed out waiting for client %u (%u ms), dropping",
					i, (unsigned)(g_now_ms - cinfo[i].started_ms));
				close_client(i);
			}
		}

		if (!cnt_closed)
			continue;

		/* We closed at least one client, coalesce pfd[], cinfo[] */
		if (min_closed + cnt_closed >= num_clients) {
			/* clients [min_closed..num_clients-1] are all closed */
			/* log(L_DEBUG, "taking shortcut"); - almost always happens */
			goto coalesce_done;
		}
		j = min_closed;
		i = min_closed + 1;
		while (i < num_clients) {
			while (1) {
				if (pfd[i].fd)
					break;
				if (++i >= num_clients)
					goto coalesce_done;
			}
			pfd[j] = pfd[i];
			cinfo[j++] = cinfo[i++];
		}

 coalesce_done:
		num_clients -= cnt_closed;
		log(L_DEBUG, "removing %d closed clients. clients:%d", cnt_closed, num_clients);
		min_closed = INT_MAX;
		cnt_closed = 0;
		/* start accepting new connects */
		pfd[0].events = POLLIN;
		pfd[1].events = POLLIN;
	} /* while (1) */
}


/*
** Initialization
*/

#define NSCD_PIDFILE    "/var/run/nscd/nscd.pid"
#define NSCD_DIR        "/var/run/nscd"
#define NSCD_SOCKET     "/var/run/nscd/socket"
#define NSCD_SOCKET_OLD "/var/run/.nscd_socket"

static smallint wrote_pidfile;

static void cleanup_on_signal(int sig)
{
	if (wrote_pidfile)
		unlink(NSCD_PIDFILE);
	unlink(NSCD_SOCKET_OLD);
	unlink(NSCD_SOCKET);
	exit(0);
}

static void write_pid(void)
{
	FILE *pid = fopen(NSCD_PIDFILE, "w");
	if (!pid)
		return;
	fprintf(pid, "%d\n", getpid());
	fclose(pid);
	wrote_pidfile = 1;
}

/* Open a listening nscd server socket */
static int open_socket(const char *name)
{
	struct sockaddr_un sun;
	int sock = socket(AF_UNIX, SOCK_STREAM, 0);
	if (sock < 0)
		perror_and_die("cannot create unix domain socket");
	ndelay_on(sock);
	close_on_exec(sock);
	sun.sun_family = AF_UNIX;
	strcpy(sun.sun_path, name);
	unlink(name);
	if (bind(sock, (struct sockaddr *) &sun, sizeof(sun)) < 0)
		perror_and_die("bind(%s)", name);
	if (chmod(name, 0666) < 0)
		perror_and_die("chmod(%s)", name);
	if (listen(sock, (max_reqnum/8) | 1) < 0)
		perror_and_die("listen");
	return sock;
}

static const struct option longopt[] = {
	/* name, has_arg, int *flag, int val */
	{ "debug"      , no_argument      , NULL, 'd' },
	{ "config-file", required_argument, NULL, 'f' },
	{ "invalidate" , required_argument, NULL, 'i' },
	{ "shutdown"   , no_argument      , NULL, 'K' },
	{ "nthreads"   , required_argument, NULL, 't' },
	{ "version"    , no_argument      , NULL, 'V' },
	{ "help"       , no_argument      , NULL, '?' },
	{ "usage"      , no_argument      , NULL, '?' },
	/* just exit(0). TODO: "test" connect? */
	{ "statistic"  , no_argument      , NULL, 'g' },
	{ "secure"     , no_argument      , NULL, 'S' }, /* ? */
	{ }
};

static const char *const help[] = {
	"Do not daemonize; log to stderr",
	"File to read configuration from",
	"Invalidate cache",
	"Shut the server down",
	"Serve N requests in parallel",
	"Version",
};

static void print_help_and_die(void)
{
	const struct option *opt = longopt;
	const char *const *h = help;

	puts("Usage: nscd [OPTION...]\n"
	     "Name Service Cache Daemon\n");
	do {
		printf("\t" "-%c,--%-11s %s\n", opt->val, opt->name, *h);
		h++;
		opt++;
	} while (opt->val != '?');
	exit(1);
}

static char *skip_service(int *srv, const char *s)
{
	if (strcmp("passwd", s) == 0) {
		*srv = SRV_PASSWD;
		s++;
	} else if (strcmp("group", s) == 0) {
		*srv = SRV_GROUP;
	} else if (strcmp("hosts", s) == 0) {
		*srv = SRV_HOSTS;
	} else {
		return NULL;
	}
	return skip_whitespace(s + 6);
}

static void handle_null(const char *str, int srv) {}

static void handle_logfile(const char *str, int srv)
{
	config.logfile = xstrdup(str);
}

static void handle_debuglvl(const char *str, int srv)
{
	debug |= (uint8_t) getnum(str);
}

static void handle_threads(const char *str, int srv)
{
	unsigned n = getnum(str);
	if (max_reqnum < n)
		max_reqnum = n;
}

static void handle_user(const char *str, int srv)
{
	config.user = xstrdup(str);
}

static void handle_enable(const char *str, int srv)
{
	config.srv_enable[srv] = ((str[0] | 0x20) == 'y');
}

static void handle_pttl(const char *str, int srv)
{
	config.pttl[srv] = getnum(str);
}

static void handle_nttl(const char *str, int srv)
{
	config.nttl[srv] = getnum(str);
}

static void handle_size(const char *str, int srv)
{
	config.size[srv] = getnum(str);
}

static void handle_chfiles(const char *str, int srv)
{
	config.check_files[srv] = ((str[0] | 0x20) == 'y');
}

static void parse_conffile(const char *conffile, int warn)
{
	static const struct confword {
		const char *str;
		void (*handler)(const char *, int);
	} conf_words[] = {
		{ "_" "logfile"               , handle_logfile  },
		{ "_" "debug-level"           , handle_debuglvl },
		{ "_" "threads"               , handle_threads  },
		{ "_" "max-threads"           , handle_threads  },
		{ "_" "server-user"           , handle_user     },
		/* ignore: any user can stat */
		{ "_" "stat-user"             , handle_null     },
		{ "_" "paranoia"              , handle_null     }, /* ? */
		/* ignore: design goal is to never crash/hang */
		{ "_" "reload-count"          , handle_null     },
		{ "_" "restart-interval"      , handle_null     },
		{ "S" "enable-cache"          , handle_enable   },
		{ "S" "positive-time-to-live" , handle_pttl     },
		{ "S" "negative-time-to-live" , handle_nttl     },
		{ "S" "suggested-size"        , handle_size     },
		{ "S" "check-files"           , handle_chfiles  },
		{ "S" "persistent"            , handle_null     }, /* ? */
		{ "S" "shared"                , handle_null     }, /* ? */
		{ "S" "auto-propagate"        , handle_null     }, /* ? */
		{ }
	};

	char buf[128];
	FILE *file = fopen(conffile, "r");
	int lineno = 0;

	if (!file) {
		if (conffile != default_conffile)
			perror_and_die("cannot open %s", conffile);
		return;
	}

	while (fgets(buf, sizeof(buf), file) != NULL) {
		const struct confword *word;
		char *p;
		int len = strlen(buf);

		lineno++;
		if (len) {
			if (buf[len-1] != '\n') {
				if (len >= sizeof(buf) - 1)
					error_and_die("%s:%d: line is too long", conffile, lineno);
				len++; /* last line, not terminated by '\n' */
			}
			buf[len-1] = '\0';
		}
		p = strchr(buf, '#');
		if (p)
			*p = '\0';

		p = skip_whitespace(buf);
		if (!*p)
			continue;
		*skip_non_whitespace(p) = '\0';
		word = conf_words;
		while (1) {
			if (strcmp(word->str + 1, p) == 0) {
				int srv = 0;
				p = skip_whitespace(p + strlen(p) + 1);
				*skip_non_whitespace(p) = '\0';
				if (word->str[0] == 'S') {
					char *p2 = skip_service(&srv, p);
					if (!p2) {
						if (warn)
							error("%s:%d: ignoring unknown service name '%s'", conffile, lineno, p);
						break;
					}
					p = p2;
					*skip_non_whitespace(p) = '\0';
				}
				word->handler(p, srv);
				break;
			}
			word++;
			if (!word->str) {
				if (warn)
					error("%s:%d: ignoring unknown directive '%s'", conffile, lineno, p);
				break;
			}
		}
	}
	fclose(file);
}


/* "XX,XX[,XX]..." -> gid_t[] */
static gid_t* env_U_to_uid_and_gids(const char *str, int *sizep)
{
	const char *sp;
	gid_t *ug, *gp;
	int ng;

	sp = str;
	ng = 1;
	while (*sp)
		if (*sp++ == ',')
			ng++;
	ug = xmalloc(ng * sizeof(ug[0]));

	ng = 0;
	gp = ug;
	sp = str;
	errno = 0;
	while (1) {
		ng++;
		*gp++ = strtoul(sp, (char**)&sp, 16);
		if (errno || (*sp != ',' && *sp != '\0'))
			error_and_die("internal error");
		if (*sp == '\0')
			break;
		sp++;
	}

	*sizep = ng;
	return ug;
}


static char* user_to_env_U(const char *user)
{
	int ng;
	char *ug_str, *sp;
	gid_t *ug, *gp;
	struct passwd *pw;

	pw = getpwnam(user);
	if (!pw)
		perror_and_die("user '%s' is not known", user);

	ng = 64;
	/* 0th cell will be used for uid */
	ug = xmalloc((1 + ng) * sizeof(ug[0]));
	if (getgrouplist(user, pw->pw_gid, &ug[1], &ng) < 0) {
		ug = xrealloc(ug, (1 + ng) * sizeof(ug[0]));
		if (getgrouplist(user, pw->pw_gid, &ug[1], &ng) < 0)
			perror_and_die("can't get groups of user '%s'", user);
	}
	ng++;
	ug[0] = pw->pw_uid;

	/* How much do we need for "-Uxx,xx[,xx]..." string? */
	ug_str = xmalloc((sizeof(unsigned long)+1)*2 * ng + 3);
	gp = ug;
	sp = ug_str;
	*sp++ = 'U';
	*sp++ = '=';
	do {
		sp += sprintf(sp, "%lx,", (unsigned long)(*gp++));
	} while (--ng);
	sp[-1] = '\0';

	free(ug);
	return ug_str;
}


/* not static - don't inline me, compiler! */
void readlink_self_exe(void)
{
	char buf[PATH_MAX + 1];
	ssize_t sz = readlink("/proc/self/exe", buf, sizeof(buf) - 1);
	if (sz < 0)
		perror_and_die("readlink %s failed", "/proc/self/exe");
	buf[sz] = 0;
	self_exe_points_to = xstrdup(buf);
}


static void special_op(const char *arg) NORETURN;
static void special_op(const char *arg)
{
	static const user_req_header ureq = { NSCD_VERSION, SHUTDOWN, 0 };

	struct sockaddr_un addr;
	int sock;

	sock = socket(PF_UNIX, SOCK_STREAM, 0);
	if (sock < 0)
		error_and_die("cannot create AF_UNIX socket");

	addr.sun_family = AF_UNIX;
	strcpy(addr.sun_path, NSCD_SOCKET);
	if (connect(sock, (struct sockaddr *) &addr, sizeof(addr)) < 0)
		error_and_die("cannot connect to %s", NSCD_SOCKET);

	if (!arg) { /* shutdown */
		xfull_write(sock, &ureq, sizeof(ureq));
		printf("sent shutdown request, exiting\n");
	} else { /* invalidate */
		size_t arg_len = strlen(arg) + 1;
		struct {
			user_req_header req;
			char arg[arg_len];
		} reqdata;
		reqdata.req.version = NSCD_VERSION;
		reqdata.req.type = INVALIDATE;
		reqdata.req.key_len = arg_len;
		memcpy(reqdata.arg, arg, arg_len);
		xfull_write(sock, &reqdata, arg_len + sizeof(ureq));
		printf("sent invalidate(%s) request, exiting\n", arg);
	}
	exit(0);
}


/* This internal glibc function is called to disable trying to contact nscd.
 * We _are_ nscd, so we need to do the lookups, and not recurse. */
void __nss_disable_nscd(void);

int main(int argc, char **argv)
{
	int n;
	unsigned opt_d_cnt;
	const char *env_U;
	const char *conffile;

	/* make sure we don't get recursive calls */
	__nss_disable_nscd();

	if (argv[0][0] == 'w') /* "worker_nscd" */
		worker(argv[1]);

	setlinebuf(stdout);
	setlinebuf(stderr);

	/* Make sure stdio is not closed */
	n = xopen3("/dev/null", O_RDWR, 0);
	while (n < 2)
		n = dup(n);
	/* Close unexpected open file descriptors */
	n |= 0xff; /* start from at least fd# 255 */
	do {
		close(n--);
	} while (n > 2);

	/* For idiotic kernels which disallow "exec /proc/self/exe" */
	readlink_self_exe();

	conffile = default_conffile;
	opt_d_cnt = 0;
	while ((n = getopt_long(argc, argv, "df:i:KVgt:", longopt, NULL)) != -1) {
		switch (n) {
		case 'd':
			opt_d_cnt++;
			debug &= ~D_DAEMON;
			break;
		case 'f':
			conffile = optarg;
			break;
		case 'i':
			/* invalidate */
			special_op(optarg); /* exits */
		case 'K':
			/* shutdown server */
			special_op(NULL); /* exits */
		case 'V':
			puts("unscd - nscd which does not hang, v."PROGRAM_VERSION);
			exit(0);
		case 'g':
			exit(0);
		case 't':
			/* N threads */
			max_reqnum = getnum(optarg);
			break;
		case 'S':
			/* secure (?) */
			break;
		default:
			print_help_and_die();
		}
	}
	/* Multiple -d can bump debug regardless of nscd.conf:
	 * no -d or -d: 0, -dd: 1,
	 * -ddd: 3, -dddd: 7, -ddddd: 15
	 */
	if (opt_d_cnt != 0)
		debug |= (((1U << opt_d_cnt) >> 1) - 1) & L_ALL;

	env_U = getenv("U");
	/* Avoid duplicate warnings if $U exists */
	parse_conffile(conffile, /* warn? */ (env_U == NULL));

	/* I have a user report of (broken?) ldap nss library
	 * opening and never closing a socket to a ldap server,
	 * even across fork() and exec(). This messes up
	 * worker child's operations for the reporter.
	 *
	 * This strenghtens my belief that nscd _must not_ trust
	 * nss libs to be written correctly.
	 *
	 * Here, we need to jump through the hoops to guard against
	 * such problems. If config file has server-user setting, we need
	 * to setgroups + setuid. For that, we need to get uid and gid vector.
	 * And that means possibly using buggy nss libs.
	 * We will do it here, but then we will re-exec, passing uid+gids
	 * in an environment variable.
	 */
	if (!env_U && config.user) {
		/* user_to_env_U() does getpwnam and getgrouplist */
		if (putenv(user_to_env_U(config.user)))
			error_and_die("out of memory");
		/* fds leaked by nss will be closed by execed copy */
		execv(self_exe_points_to, argv);
		xexecve("/proc/self/exe", argv, environ);
	}

	/* Allocate dynamically sized stuff */
	max_reqnum += 2; /* account for 2 first "fake" clients */
	if (max_reqnum < 8) max_reqnum = 8; /* sanitize */
	/* Since refcount is a byte, can't serve more than 255-2 clients
	 * at once. The rest will block in connect() */
	if (max_reqnum > 0xff) max_reqnum = 0xff;
	client_buf = xzalloc(max_reqnum * sizeof(client_buf[0]));
	busy_cbuf  = xzalloc(max_reqnum * sizeof(busy_cbuf[0]));
	pfd        = xzalloc(max_reqnum * sizeof(pfd[0]));
	cinfo      = xzalloc(max_reqnum * sizeof(cinfo[0]));

	cache_size = (config.size[0] + config.size[1] + config.size[2]) / 8;
	if (cache_size < 8) cache_size = 8; /* 8*8 = 64 entries min */
	if (cache_size > 0xffff) cache_size = 0xffff; /* 8*64k entries max */
	cache_size |= 1; /* force it to be odd */
	cache = xzalloc(cache_size * sizeof(cache[0]));

	/* Register cleanup hooks */
	signal(SIGINT, cleanup_on_signal);
	signal(SIGTERM, cleanup_on_signal);
	/* Don't die if a client closes a socket on us */
	signal(SIGPIPE, SIG_IGN);
	/* Avoid creating zombies */
	signal(SIGCHLD, SIG_IGN);
#if !DEBUG_BUILD
	/* Ensure workers don't have SIGALRM ignored */
	signal(SIGALRM, SIG_DFL);
#endif

	if (mkdir(NSCD_DIR, 0755) == 0) {
		/* prevent bad mode of NSCD_DIR if umask is e.g. 077 */
		chmod(NSCD_DIR, 0755);
	}
	pfd[0].fd = open_socket(NSCD_SOCKET);
	pfd[1].fd = open_socket(NSCD_SOCKET_OLD);
	pfd[0].events = POLLIN;
	pfd[1].events = POLLIN;

	if (debug & D_DAEMON) {
		daemon(/*nochdir*/ 1, /*noclose*/ 0);
		if (config.logfile) {
			/* nochdir=1: relative paths still work as expected */
			xmovefd(xopen3(config.logfile, O_WRONLY|O_CREAT|O_TRUNC, 0666), 2);
			debug |= D_STAMP;
		} else {
			debug = 0; /* why bother? it's /dev/null'ed anyway */
		}
		chdir("/"); /* compat */
		write_pid();
		setsid();
		/* ignore job control signals */
		signal(SIGTTOU, SIG_IGN);
		signal(SIGTTIN, SIG_IGN);
		signal(SIGTSTP, SIG_IGN);
	}

	log(L_ALL, "nscd v" PROGRAM_VERSION ", debug level 0x%x", debug & L_ALL);
	log(L_DEBUG, "max %u requests in parallel", max_reqnum - 2);
	log(L_DEBUG, "cache size %u x 8 entries", cache_size);

	if (env_U) {
		int size;
		gid_t *ug = env_U_to_uid_and_gids(env_U, &size);
		if (size > 1)
			if (setgroups(size - 1, &ug[1]) || setgid(ug[1]))
				perror_and_die("cannot set groups for user '%s'", config.user);
		if (size > 0)
			if (setuid(ug[0]))
				perror_and_die("cannot set uid to %u", (unsigned)(ug[0]));
		free(ug);
	}

	for (n = 0; n < 3; n++) {
		log(L_DEBUG, "%s cache enabled:%u pttl:%u nttl:%u",
				srv_name[n],
				config.srv_enable[n],
				config.pttl[n],
				config.nttl[n]);
		config.pttl[n] *= 1000;
		config.nttl[n] *= 1000;
	}

	main_loop();

	return 0;
}

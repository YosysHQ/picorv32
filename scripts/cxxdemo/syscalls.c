// An extremely minimalist syscalls.c for newlib
// Based on riscv newlib libgloss/riscv/machine/syscall.h
// Written by Clifford Wolf.

#include <sys/stat.h>
#include <unistd.h>
#include <errno.h>

#define UNIMPL_FUNC(_f) ".globl " #_f "\n.type " #_f ", @function\n" #_f ":\n"

asm (
	".text\n"
	".align 2\n"
	UNIMPL_FUNC(open)
	UNIMPL_FUNC(openat)
	UNIMPL_FUNC(lseek)
	UNIMPL_FUNC(stat)
	UNIMPL_FUNC(lstat)
	UNIMPL_FUNC(fstatat)
	UNIMPL_FUNC(isatty)
	UNIMPL_FUNC(access)
	UNIMPL_FUNC(faccessat)
	UNIMPL_FUNC(link)
	UNIMPL_FUNC(unlink)
	UNIMPL_FUNC(execve)
	UNIMPL_FUNC(getpid)
	UNIMPL_FUNC(fork)
	UNIMPL_FUNC(kill)
	UNIMPL_FUNC(wait)
	UNIMPL_FUNC(times)
	UNIMPL_FUNC(gettimeofday)
	UNIMPL_FUNC(ftime)
	UNIMPL_FUNC(utime)
	UNIMPL_FUNC(chown)
	UNIMPL_FUNC(chmod)
	UNIMPL_FUNC(chdir)
	UNIMPL_FUNC(getcwd)
	UNIMPL_FUNC(sysconf)
	"j unimplemented_syscall\n"
);

void unimplemented_syscall()
{
	const char *p = "Unimplemented system call called!\n";
	while (*p)
		*(volatile int*)0x10000000 = *(p++);
	asm volatile ("ebreak");
	__builtin_unreachable();
}

ssize_t read(int file, void *ptr, size_t len)
{
	// always EOF
	return 0;
}

ssize_t write(int file, const void *ptr, size_t len)
{
	const void *eptr = ptr + len;
	while (ptr != eptr)
		*(volatile int*)0x10000000 = *(char*)(ptr++);
	return len;
}

int close(int file)
{
	// close is called before _exit()
	return 0;
}

int fstat(int file, struct stat *st)
{
	// fstat is called during libc startup
	errno = ENOENT;
	return -1;
}

void *sbrk(ptrdiff_t incr)
{
	extern unsigned char _end[];	// Defined by linker
	static unsigned long heap_end;

	if (heap_end == 0)
		heap_end = (long)_end;

	heap_end += incr;
	return (void *)(heap_end - incr);
}

void _exit(int exit_status)
{
	asm volatile ("ebreak");
	__builtin_unreachable();
}


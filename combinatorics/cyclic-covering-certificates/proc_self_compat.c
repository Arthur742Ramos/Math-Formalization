/* Compatibility for the managed executor's /proc layout.
 * Lean 4.19.0 asks readlink("/proc/<own-pid>/exe"); this executor provides
 * /proc/self/exe but no numeric PID directory. Map that exact own-PID path
 * to its POSIX-equivalent self path. No theorem-prover code is changed.
 * Build: cc -shared -fPIC -O2 -o proc_self_compat.so proc_self_compat.c -ldl
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>
ssize_t readlink(const char *path, char *buf, size_t bufsiz) {
    static ssize_t (*original_readlink)(const char *, char *, size_t);
    if (!original_readlink)
        original_readlink = dlsym(RTLD_NEXT, "readlink");
    char own_exe[64];
    snprintf(own_exe, sizeof(own_exe), "/proc/%ld/exe", (long)getpid());
    if (strcmp(path, own_exe) == 0)
        return original_readlink("/proc/self/exe", buf, bufsiz);
    return original_readlink(path, buf, bufsiz);
}

#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

/* Lean 4.34.1 discovers its own executable through /proc/<getpid()>/exe.
 * This container exposes the equivalent /proc/self/exe, while numeric PID
 * paths are unavailable. Only self-executable discovery is redirected;
 * no Lean code, proof checking, or other filesystem access is changed. */
ssize_t readlink(const char *path, char *buf, size_t size) {
    static ssize_t (*original)(const char *, char *, size_t);
    if (!original) original = dlsym(RTLD_NEXT, "readlink");
    char own[64];
    snprintf(own, sizeof own, "/proc/%ld/exe", (long)getpid());
    return original(strcmp(path, own) == 0 ? "/proc/self/exe" : path, buf, size);
}

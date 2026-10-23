#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
/* Runtime compatibility: this container exposes /proc/self/exe but its
   virtual PID is not present under /proc/<pid>. No Lean logic is changed. */
ssize_t readlink(const char *path, char *buf, size_t size) {
  static ssize_t (*real_readlink)(const char *, char *, size_t);
  if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
  char own[64];
  snprintf(own, sizeof(own), "/proc/%d/exe", getpid());
  return real_readlink(strcmp(path, own) == 0 ? "/proc/self/exe" : path, buf, size);
}

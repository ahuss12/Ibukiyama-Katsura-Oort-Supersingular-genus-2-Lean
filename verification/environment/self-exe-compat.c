#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
/* The executor has a PID namespace but /proc shows host PIDs. Redirect only
   this process's executable lookup to the permitted /proc/self/exe alias. */
ssize_t readlink(const char *path, char *buffer, size_t size) {
    ssize_t (*real_readlink)(const char *, char *, size_t) = dlsym(RTLD_NEXT, "readlink");
    char self_path[64];
    snprintf(self_path, sizeof self_path, "/proc/%d/exe", (int)getpid());
    return real_readlink(strcmp(path, self_path) == 0 ? "/proc/self/exe" : path,
                         buffer, size);
}

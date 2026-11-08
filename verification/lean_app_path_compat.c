/*
 * Runtime-only compatibility for this container's PID/procfs mismatch.
 * Lean 4.34.0-rc2 queries /proc/<getpid()>/exe, which does not exist here;
 * /proc/self/exe correctly identifies the same process. Only readlink of
 * this process's own executable is redirected to its equivalent self path.
 * No parser, elaborator, tactic, kernel, or axiom is modified.
 * This file is not needed on the user's normal macOS installation.
 */
#define _GNU_SOURCE
#include <limits.h>
#include <unistd.h>
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>

ssize_t readlink(const char *path, char *buf, size_t size) {
    typedef ssize_t (*original_fn)(const char *, char *, size_t);
    original_fn original = (original_fn)dlsym(RTLD_NEXT, "readlink");
    char own_exe[64];
    snprintf(own_exe, sizeof(own_exe), "/proc/%d/exe", (int)getpid());
    if (strcmp(path, own_exe) == 0)
        path = "/proc/self/exe";
    return original(path, buf, size);
}

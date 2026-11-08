#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>
#include <fcntl.h>
ssize_t readlink(const char *path, char *buffer, size_t size) {
    ssize_t (*orig)(const char *, char *, size_t) = dlsym(RTLD_NEXT, "readlink");
    char self[64]; snprintf(self,sizeof self,"/proc/%d/exe",(int)getpid());
    return orig(strcmp(path,self)==0?"/proc/self/exe":path,buffer,size);
}
void *mmap(void *addr,size_t length,int prot,int flags,int fd,off_t offset) {
    void *(*orig)(void*,size_t,int,int,int,off_t)=dlsym(RTLD_NEXT,"mmap");
    void *p=orig(addr,length,prot,flags,fd,offset);
    if(p!=MAP_FAILED && fd>=0 && (prot&PROT_READ)) {
      char name[64],path[4096]; snprintf(name,sizeof name,"/proc/self/fd/%d",fd);
      ssize_t n=readlink(name,path,sizeof path-1);
      if(n>0) {path[n]=0;if(strstr(path,".olean")) { madvise(p,length,MADV_RANDOM); madvise(p,length,MADV_NOHUGEPAGE); }}
    }
    return p;
}

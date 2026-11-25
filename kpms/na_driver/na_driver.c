/* SPDX-License-Identifier: GPL-2.0-or-later */
// na_driver.c — Official KernelPatch Module (Hardened)

#include <compiler.h>
#include <kpmodule.h>
#include <common.h>
#include <kputils.h>
#include <syscall.h>
#include <hook.h>
#include <kallsyms.h>
#include <linux/errno.h>
#include <linux/uaccess.h>
#include <linux/string.h>
#include <uapi/asm-generic/unistd.h>

#ifndef __pid_t_defined
typedef int pid_t;
#define __pid_t_defined
#endif

struct task_struct;

#define FOLL_WRITE       0x01
#define PRCTL_MAGIC      0x4E41
#define CMD_READ_MEM     1
#define CMD_WRITE_MEM    2
#define CMD_GET_PID      5
#define MAX_RW_SIZE      4096
#define MAX_PKG_NAME     256
#define CHUNK_BUF_SIZE   512

KPM_NAME("NinMods");
KPM_VERSION("1.0.0");
KPM_LICENSE("GPL v2");
KPM_AUTHOR("@cache_file");
KPM_DESCRIPTION("KernelPatch Process Memory R/W Driver");

struct na_cmd {
    uint32_t op;
    uint32_t pid;
    uint64_t addr;
    uint32_t size;
    int32_t  result;
    int32_t  screen_w;
    int32_t  screen_h;
    char     pkg[MAX_PKG_NAME];
    uint8_t  data[MAX_RW_SIZE];
};

// Header-only view to keep kernel stack usage small
struct na_cmd_hdr {
    uint32_t op;
    uint32_t pid;
    uint64_t addr;
    uint32_t size;
    int32_t  result;
    int32_t  screen_w;
    int32_t  screen_h;
    char     pkg[MAX_PKG_NAME];
};

static struct task_struct *(*kf_find_task_by_vpid)(pid_t) = 0;
static int (*kf_access_process_vm)(struct task_struct *, unsigned long, void *, int, unsigned int) = 0;

static uint64_t g_comm_offset = 0;
static volatile int g_in_flight = 0;
static volatile int g_exiting = 0;
static int g_use_inline_hook = 0;
static int g_hooked = 0;

static void na_memcpy(void *dst, const void *src, uint32_t n)
{
    uint8_t *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;
    uint32_t i;
    for (i = 0; i < n; i++) d[i] = s[i];
}

static int na_strncmp(const char *a, const char *b, uint32_t n)
{
    uint32_t i;
    for (i = 0; i < n; i++) {
        if (a[i] != b[i]) return (unsigned char)a[i] - (unsigned char)b[i];
        if (!a[i]) break;
    }
    return 0;
}

static void detect_comm_offset(void)
{
    uint8_t *init_t = (uint8_t *)(unsigned long)kallsyms_lookup_name("init_task");
    uint64_t off;
    if (!init_t) return;
    for (off = 0x300; off < 0xC00; off += 4) {
        if (na_strncmp((const char *)(init_t + off), "swapper/0", 10) == 0) {
            g_comm_offset = off;
            return;
        }
    }
}

static int read_mem_chunked(uint32_t pid, uint64_t addr, uint8_t __user *udata, uint32_t size)
{
    struct task_struct *task;
    uint8_t buf[CHUNK_BUF_SIZE];
    uint32_t done = 0;

    if (!kf_find_task_by_vpid || !kf_access_process_vm) return -ENOSYS;
    if (addr < 0x10000ULL || size == 0 || size > MAX_RW_SIZE) return -EINVAL;

    task = kf_find_task_by_vpid((pid_t)pid);
    if (!task) return -ESRCH;

    while (done < size) {
        uint32_t chunk = size - done;
        int n;
        if (chunk > CHUNK_BUF_SIZE) chunk = CHUNK_BUF_SIZE;
        n = kf_access_process_vm(task, (unsigned long)(addr + done), buf, (int)chunk, 0);
        if (n <= 0) return -EIO;
        if (compat_copy_to_user(udata + done, buf, (uint32_t)n) != 0) return -EFAULT;
        done += (uint32_t)n;
        if ((uint32_t)n < chunk) break;
    }
    return (done == size) ? 0 : -EIO;
}

static int write_mem_chunked(uint32_t pid, uint64_t addr, const uint8_t __user *udata, uint32_t size)
{
    struct task_struct *task;
    uint8_t buf[CHUNK_BUF_SIZE];
    uint32_t done = 0;

    if (!kf_find_task_by_vpid || !kf_access_process_vm) return -ENOSYS;
    if (addr < 0x10000ULL || size == 0 || size > MAX_RW_SIZE) return -EINVAL;

    task = kf_find_task_by_vpid((pid_t)pid);
    if (!task) return -ESRCH;

    while (done < size) {
        uint32_t chunk = size - done;
        int n;
        if (chunk > CHUNK_BUF_SIZE) chunk = CHUNK_BUF_SIZE;
        if (compat_copy_from_user(buf, udata + done, chunk) != 0) return -EFAULT;
        n = kf_access_process_vm(task, (unsigned long)(addr + done), buf, (int)chunk, FOLL_WRITE);
        if (n <= 0) return -EIO;
        done += (uint32_t)n;
        if ((uint32_t)n < chunk) break;
    }
    return (done == size) ? 0 : -EIO;
}

static int32_t get_pid_by_package(const char *pkg)
{
    int32_t pid;
    struct task_struct *task;
    char comm[16];
    if (!kf_find_task_by_vpid || !g_comm_offset || !pkg || !pkg[0]) return -1;
    for (pid = 1; pid < 32768; pid++) {
        task = kf_find_task_by_vpid((pid_t)pid);
        if (!task) continue;
        na_memcpy(comm, (const char *)task + g_comm_offset, 15);
        comm[15] = '\0';
        if (na_strncmp(comm, pkg, 15) == 0) return pid;
    }
    return -1;
}

void before_prctl(hook_fargs5_t *args, void *udata)
{
    int option;
    int subcmd;
    struct na_cmd __user *ucmd;
    struct na_cmd_hdr hdr;

    if (__atomic_load_n(&g_exiting, __ATOMIC_ACQUIRE)) return;

    option = (int)syscall_argn(args, 0);
    if (option != PRCTL_MAGIC) return;

    __atomic_add_fetch(&g_in_flight, 1, __ATOMIC_ACQUIRE);

    subcmd = (int)syscall_argn(args, 1);
    ucmd   = (struct na_cmd __user *)(unsigned long)syscall_argn(args, 2);

    if (!ucmd) goto out;
    if (compat_copy_from_user(&hdr, ucmd, sizeof(hdr)) != 0) goto out;

    hdr.result = -ENOSYS;

    switch (subcmd) {
    case CMD_READ_MEM:
        hdr.result = read_mem_chunked(hdr.pid, hdr.addr, ucmd->data, hdr.size);
        break;
    case CMD_WRITE_MEM:
        hdr.result = write_mem_chunked(hdr.pid, hdr.addr, ucmd->data, hdr.size);
        break;
    case CMD_GET_PID:
        hdr.pkg[MAX_PKG_NAME - 1] = '\0';
        hdr.pid    = (uint32_t)get_pid_by_package(hdr.pkg);
        hdr.result = ((int32_t)hdr.pid > 0) ? 0 : -ESRCH;
        break;
    default:
        hdr.result = -EINVAL;
        break;
    }

    compat_copy_to_user(ucmd, &hdr, sizeof(hdr));

out:
    args->ret = 0;
    args->skip_origin = 1;
    __atomic_sub_fetch(&g_in_flight, 1, __ATOMIC_RELEASE);
}

static long na_init(const char *args, const char *event, void *__user reserved)
{
    hook_err_t err;

    kf_find_task_by_vpid = (typeof(kf_find_task_by_vpid))kallsyms_lookup_name("find_task_by_vpid");
    if (!kf_find_task_by_vpid)
        kf_find_task_by_vpid = (typeof(kf_find_task_by_vpid))kallsyms_lookup_name("find_task_by_pid_ns");

    kf_access_process_vm = (typeof(kf_access_process_vm))kallsyms_lookup_name("access_process_vm");
    detect_comm_offset();

    err = inline_hook_syscalln(__NR_prctl, 5, before_prctl, 0, 0);
    if (err == HOOK_NO_ERR) {
        g_use_inline_hook = 1;
        g_hooked = 1;
        return 0;
    }

    err = fp_hook_syscalln(__NR_prctl, 5, before_prctl, 0, 0);
    if (err == HOOK_NO_ERR) {
        g_use_inline_hook = 0;
        g_hooked = 1;
    }
    return 0;
}

static long na_ctl0(const char *ctl_args, char *__user out_msg, int outlen)
{
    return 0;
}

static long na_exit(void *__user reserved)
{
    int tries = 0;
    __atomic_store_n(&g_exiting, 1, __ATOMIC_RELEASE);

    if (g_hooked) {
        if (g_use_inline_hook)
            inline_unhook_syscalln(__NR_prctl, before_prctl, 0);
        else
            fp_unhook_syscalln(__NR_prctl, before_prctl, 0);
        g_hooked = 0;
    }

    while (__atomic_load_n(&g_in_flight, __ATOMIC_ACQUIRE) > 0 && tries < 1000000) {
        tries++;
    }
    return 0;
}

KPM_INIT(na_init);
KPM_CTL0(na_ctl0);
KPM_EXIT(na_exit);

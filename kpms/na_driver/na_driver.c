/* SPDX-License-Identifier: GPL-2.0-or-later */
// na_driver.c — Official KernelPatch Module (Hardened)

#include <compiler.h>
#include <kpmodule.h>
#include <linux/printk.h>
#include <uapi/asm-generic/unistd.h>
#include <linux/uaccess.h>
#include <syscall.h>
#include <linux/string.h>
#include <kputils.h>
#include <kallsyms.h>
#include <linux/errno.h>

#ifndef __pid_t_defined
typedef int pid_t;
#define __pid_t_defined
#endif

#include <linux/mm_types.h>

struct task_struct;
struct pid;

struct task_struct_offset {
    int16_t pid_offset;
    int16_t tgid_offset;
    int16_t thread_pid_offset;
    int16_t ptracer_cred_offset;
    int16_t real_cred_offset;
    int16_t cred_offset;
    int16_t comm_offset;
    int16_t fs_offset;
    int16_t files_offset;
    int16_t loginuid_offset;
    int16_t sessionid_offset;
    int16_t seccomp_offset;
    int16_t security_offset;
    int16_t stack_offset;
    int16_t tasks_offset;
    int16_t mm_offset;
    int16_t active_mm_offset;
};

extern struct task_struct_offset task_struct_offset;
extern uint64_t pgtable_phys(uint64_t pgd, uint64_t va);
extern uint64_t *pgtable_entry(uint64_t pgd, uint64_t va);

#define FOLL_WRITE       0x01
#define PTE_VALID_BIT    (1ULL << 0)
#define PTE_RDONLY_BIT   (1ULL << 7)
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

static unsigned long (*kf_copy_from_user)(void *, const void __user *, unsigned long) = 0;
static struct task_struct *(*kf_find_task_by_vpid)(pid_t) = 0;
static struct pid *(*kf_find_get_pid)(pid_t) = 0;
static struct task_struct *(*kf_get_pid_task)(struct pid *, int) = 0;
static void (*kf_put_pid)(struct pid *) = 0;
static void (*kf_put_task_struct)(struct task_struct *) = 0;
static struct mm_struct *(*kf_get_task_mm)(struct task_struct *) = 0;
static void (*kf_mmput)(struct mm_struct *) = 0;
static int (*kf_access_process_vm)(struct task_struct *, unsigned long, void *, int, unsigned int) = 0;

static void *g_init_mm = 0;
static uint64_t g_linear_voffset = 0;
static uint64_t g_page_size = 4096;
static int g_phys_ready = 0;

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

static unsigned long safe_copy_from_user(void *dst, const void __user *src, unsigned long n)
{
    if (!kf_copy_from_user) return n;
    return kf_copy_from_user(dst, src, n);
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
static inline int na_atomic_read(volatile int *p)
{
    int v = *p;
    __asm__ volatile("dmb ish" ::: "memory");
    return v;
}

static inline void na_atomic_set(volatile int *p, int v)
{
    __asm__ volatile("dmb ish" ::: "memory");
    *p = v;
}

static inline void na_atomic_inc(volatile int *p)
{
    int tmp;
    int res;
    __asm__ volatile(
        "1: ldxr %w0, [%2]\n"
        "   add  %w0, %w0, #1\n"
        "   stxr %w1, %w0, [%2]\n"
        "   cbnz %w1, 1b\n"
        "   dmb  ish\n"
        : "=&r"(tmp), "=&r"(res)
        : "r"(p)
        : "memory");
}

static inline void na_atomic_dec(volatile int *p)
{
    int tmp;
    int res;
    __asm__ volatile(
        "   dmb  ish\n"
        "1: ldxr %w0, [%2]\n"
        "   sub  %w0, %w0, #1\n"
        "   stxr %w1, %w0, [%2]\n"
        "   cbnz %w1, 1b\n"
        "   dmb  ish\n"
        : "=&r"(tmp), "=&r"(res)
        : "r"(p)
        : "memory");
}

static struct task_struct *acquire_task(pid_t pid, int *refcounted)
{
    *refcounted = 0;
    if (kf_find_get_pid && kf_get_pid_task && kf_put_pid && kf_put_task_struct) {
        struct pid *kpid = kf_find_get_pid(pid);
        struct task_struct *task;
        if (!kpid) return 0;
        task = kf_get_pid_task(kpid, 0);
        kf_put_pid(kpid);
        if (task) *refcounted = 1;
        return task;
    }
    if (kf_find_task_by_vpid) return kf_find_task_by_vpid(pid);
    return 0;
}

static void release_task(struct task_struct *task, int refcounted)
{
    if (task && refcounted && kf_put_task_struct) {
        kf_put_task_struct(task);
    }
}

static int calibrate_phys_rw(struct task_struct *sample_task)
{
    uint64_t init_pgd;
    uint64_t va;
    uint64_t pa;
    uint64_t cand;

    if (na_atomic_read(&g_phys_ready)) return 1;
    if (!g_init_mm || mm_struct_offset.pgd_offset < 0 || !sample_task) return 0;

    init_pgd = *(uint64_t *)((uintptr_t)g_init_mm + mm_struct_offset.pgd_offset);
    if (!init_pgd) return 0;

    va = ((uint64_t)sample_task) | (0xFFULL << 56);
    pa = pgtable_phys(init_pgd, va);
    if (!pa) return 0;

    cand = va - pa;
    if (((pa + cand) & 0x00FFFFFFFFFFFFFFULL) != ((uint64_t)sample_task & 0x00FFFFFFFFFFFFFFULL)) {
        return 0;
    }
    if (*(volatile uint64_t *)(pa + cand) != *(volatile uint64_t *)sample_task) {
        return 0;
    }

    g_linear_voffset = cand;
    na_atomic_set(&g_phys_ready, 1);
    return 1;
}

static uint64_t acquire_task_pgd(struct task_struct *task, struct mm_struct **out_mm, int *mm_ref)
{
    struct mm_struct *mm = 0;
    *out_mm = 0;
    *mm_ref = 0;

    if (!task || mm_struct_offset.pgd_offset < 0) return 0;

    if (kf_get_task_mm && kf_mmput) {
        mm = kf_get_task_mm(task);
        if (!mm) return 0;
        *out_mm = mm;
        *mm_ref = 1;
    } else if (task_struct_offset.mm_offset >= 0) {
        mm = *(struct mm_struct **)((uintptr_t)task + task_struct_offset.mm_offset);
        if (!mm) return 0;
        *out_mm = mm;
    } else {
        return 0;
    }

    return *(uint64_t *)((uintptr_t)mm + mm_struct_offset.pgd_offset);
}

static void release_task_mm(struct mm_struct *mm, int mm_ref)
{
    if (mm && mm_ref && kf_mmput) {
        kf_mmput(mm);
    }
}

static void na_phys_copy(void *dst, const void *src, uint32_t len)
{
    uint8_t *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;
    while (len >= 8 && (((uintptr_t)d | (uintptr_t)s) & 7ULL) == 0) {
        *(uint64_t *)d = *(const uint64_t *)s;
        d += 8;
        s += 8;
        len -= 8;
    }
    while (len--) {
        *d++ = *s++;
    }
}

static int try_phys_rw_chunk(uint64_t pgd, uint64_t va, void *kbuf, uint32_t chunk, int is_write)
{
    uint64_t pa;
    uint64_t *ptep;
    uint64_t pte;
    void *kva;

    if (!na_atomic_read(&g_phys_ready) || !pgd) return 0;

    pa = pgtable_phys(pgd, va);
    if (!pa) return 0;

    ptep = pgtable_entry(pgd, va);
    if (!ptep) return 0;

    pte = *ptep;
    if (!(pte & PTE_VALID_BIT)) return 0;
    if (is_write && (pte & PTE_RDONLY_BIT)) return 0;

    kva = (void *)(pa + g_linear_voffset);
    if (is_write) {
        na_phys_copy(kva, kbuf, chunk);
        __asm__ volatile("dmb ish" ::: "memory");
    } else {
        na_phys_copy(kbuf, kva, chunk);
    }
    return 1;
}

static int read_mem_chunked(uint32_t pid, uint64_t addr, uint8_t __user *udata, uint32_t size)
{
    struct task_struct *task;
    struct mm_struct *mm = 0;
    uint64_t pgd = 0;
    int task_ref = 0;
    int mm_ref = 0;
    uint8_t buf[CHUNK_BUF_SIZE];
    uint32_t done = 0;
    int ret = 0;

    if (addr < 0x10000ULL || size == 0 || size > MAX_RW_SIZE) return -EINVAL;

    task = acquire_task((pid_t)pid, &task_ref);
    if (!task) return -ESRCH;

    if (!na_atomic_read(&g_phys_ready)) calibrate_phys_rw(task);
    if (na_atomic_read(&g_phys_ready)) pgd = acquire_task_pgd(task, &mm, &mm_ref);

    while (done < size) {
        uint64_t curr_va = addr + done;
        uint64_t page_rem = g_page_size - (curr_va & (g_page_size - 1ULL));
        uint32_t chunk = size - done;
        int n = 0;

        if (chunk > CHUNK_BUF_SIZE) chunk = CHUNK_BUF_SIZE;
        if ((uint64_t)chunk > page_rem) chunk = (uint32_t)page_rem;

        if (pgd && try_phys_rw_chunk(pgd, curr_va, buf, chunk, 0)) {
            n = (int)chunk;
        } else if (kf_access_process_vm) {
            n = kf_access_process_vm(task, (unsigned long)curr_va, buf, (int)chunk, 0);
            if (n <= 0) {
                ret = -EIO;
                break;
            }
        } else {
            ret = -EFAULT;
            break;
        }

        if (compat_copy_to_user(udata + done, buf, n) != n) {
            ret = -EFAULT;
            break;
        }
        done += (uint32_t)n;
        if ((uint32_t)n < chunk) break;
    }

    release_task_mm(mm, mm_ref);
    release_task(task, task_ref);
    if (ret != 0) return ret;
    return (done == size) ? 0 : -EIO;
}

static int write_mem_chunked(uint32_t pid, uint64_t addr, const uint8_t __user *udata, uint32_t size)
{
    struct task_struct *task;
    struct mm_struct *mm = 0;
    uint64_t pgd = 0;
    int task_ref = 0;
    int mm_ref = 0;
    uint8_t buf[CHUNK_BUF_SIZE];
    uint32_t done = 0;
    int ret = 0;

    if (addr < 0x10000ULL || size == 0 || size > MAX_RW_SIZE) return -EINVAL;

    task = acquire_task((pid_t)pid, &task_ref);
    if (!task) return -ESRCH;

    if (!na_atomic_read(&g_phys_ready)) calibrate_phys_rw(task);
    if (na_atomic_read(&g_phys_ready)) pgd = acquire_task_pgd(task, &mm, &mm_ref);

    while (done < size) {
        uint64_t curr_va = addr + done;
        uint64_t page_rem = g_page_size - (curr_va & (g_page_size - 1ULL));
        uint32_t chunk = size - done;
        int n = 0;

        if (chunk > CHUNK_BUF_SIZE) chunk = CHUNK_BUF_SIZE;
        if ((uint64_t)chunk > page_rem) chunk = (uint32_t)page_rem;

        if (safe_copy_from_user(buf, udata + done, chunk) != 0) {
            ret = -EFAULT;
            break;
        }

        if (pgd && try_phys_rw_chunk(pgd, curr_va, buf, chunk, 1)) {
            n = (int)chunk;
        } else if (kf_access_process_vm) {
            n = kf_access_process_vm(task, (unsigned long)curr_va, buf, (int)chunk, FOLL_WRITE);
            if (n <= 0) {
                ret = -EIO;
                break;
            }
        } else {
            ret = -EFAULT;
            break;
        }

        done += (uint32_t)n;
        if ((uint32_t)n < chunk) break;
    }

    release_task_mm(mm, mm_ref);
    release_task(task, task_ref);
    if (ret != 0) return ret;
    return (done == size) ? 0 : -EIO;
}

static int32_t get_pid_by_package(const char *pkg)
{
    int32_t pid;
    char comm[16];
    if (!g_comm_offset || !pkg || !pkg[0]) return -1;
    for (pid = 1; pid < 32768; pid++) {
        int ref = 0;
        struct task_struct *task = acquire_task((pid_t)pid, &ref);
        if (!task) continue;
        na_memcpy(comm, (const char *)task + g_comm_offset, 15);
        release_task(task, ref);
        comm[15] = '\0';
        if (na_strncmp(comm, pkg, 15) == 0) return pid;
    }
    return -1;
}

static inline int na_atomic_read(volatile int *p)
{
    int v = *p;
    __asm__ volatile("dmb ish" ::: "memory");
    return v;
}

static inline void na_atomic_set(volatile int *p, int v)
{
    __asm__ volatile("dmb ish" ::: "memory");
    *p = v;
}

static inline void na_atomic_inc(volatile int *p)
{
    int tmp;
    int res;
    __asm__ volatile(
        "1: ldxr %w0, [%2]\n"
        "   add  %w0, %w0, #1\n"
        "   stxr %w1, %w0, [%2]\n"
        "   cbnz %w1, 1b\n"
        "   dmb  ish\n"
        : "=&r"(tmp), "=&r"(res)
        : "r"(p)
        : "memory");
}

static inline void na_atomic_dec(volatile int *p)
{
    int tmp;
    int res;
    __asm__ volatile(
        "   dmb  ish\n"
        "1: ldxr %w0, [%2]\n"
        "   sub  %w0, %w0, #1\n"
        "   stxr %w1, %w0, [%2]\n"
        "   cbnz %w1, 1b\n"
        : "=&r"(tmp), "=&r"(res)
        : "r"(p)
        : "memory");
}

void before_prctl(hook_fargs5_t *args, void *udata)
{
    int option;
    int subcmd;
    struct na_cmd __user *ucmd;
    struct na_cmd_hdr hdr;

    if (na_atomic_read(&g_exiting)) return;

    option = (int)syscall_argn(args, 0);
    if (option != PRCTL_MAGIC) return;

    na_atomic_inc(&g_in_flight);
    if (na_atomic_read(&g_exiting)) {
        na_atomic_dec(&g_in_flight);
        return;
    }

    subcmd = (int)syscall_argn(args, 1);
    ucmd   = (struct na_cmd __user *)(unsigned long)syscall_argn(args, 2);

    if (!ucmd || safe_copy_from_user(&hdr, ucmd, sizeof(hdr)) != 0) {
        args->ret = -EFAULT;
        args->skip_origin = 1;
        na_atomic_dec(&g_in_flight);
        return;
    }

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

    (void)compat_copy_to_user(ucmd, &hdr, sizeof(hdr));

    args->ret = 0;
    args->skip_origin = 1;
    na_atomic_dec(&g_in_flight);
}

static long na_init(const char *args, const char *event, void *__user reserved)
{
    hook_err_t err;

    kf_copy_from_user = (typeof(kf_copy_from_user))kallsyms_lookup_name("__arch_copy_from_user");
    if (!kf_copy_from_user)
        kf_copy_from_user = (typeof(kf_copy_from_user))kallsyms_lookup_name("_copy_from_user");
    if (!kf_copy_from_user)
        kf_copy_from_user = (typeof(kf_copy_from_user))kallsyms_lookup_name("copy_from_user");

    kf_find_task_by_vpid = (typeof(kf_find_task_by_vpid))kallsyms_lookup_name("find_task_by_vpid");
    if (!kf_find_task_by_vpid)
        kf_find_task_by_vpid = (typeof(kf_find_task_by_vpid))kallsyms_lookup_name("find_task_by_pid_ns");

    kf_find_get_pid = (typeof(kf_find_get_pid))kallsyms_lookup_name("find_get_pid");
    kf_get_pid_task = (typeof(kf_get_pid_task))kallsyms_lookup_name("get_pid_task");
    kf_put_pid = (typeof(kf_put_pid))kallsyms_lookup_name("put_pid");
    kf_put_task_struct = (typeof(kf_put_task_struct))kallsyms_lookup_name("__put_task_struct");
    kf_get_task_mm = (typeof(kf_get_task_mm))kallsyms_lookup_name("get_task_mm");
    kf_mmput = (typeof(kf_mmput))kallsyms_lookup_name("mmput");
    g_init_mm = (void *)kallsyms_lookup_name("init_mm");

    {
        uint64_t tcr_el1 = 0;
        uint64_t tg1;
        __asm__ volatile("mrs %0, tcr_el1" : "=r"(tcr_el1));
        tg1 = (tcr_el1 >> 30) & 3ULL;
        if (tg1 == 1ULL) g_page_size = 16384ULL;
        else if (tg1 == 3ULL) g_page_size = 65536ULL;
        else g_page_size = 4096ULL;
    }

    kf_access_process_vm = (typeof(kf_access_process_vm))kallsyms_lookup_name("access_process_vm");
    detect_comm_offset();
    if (kf_find_task_by_vpid) calibrate_phys_rw(kf_find_task_by_vpid(1));

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
    na_atomic_set(&g_exiting, 1);

    if (g_hooked) {
        if (g_use_inline_hook)
            inline_unhook_syscalln(__NR_prctl, before_prctl, 0);
        else
            fp_unhook_syscalln(__NR_prctl, before_prctl, 0);
        g_hooked = 0;
    }

    while (na_atomic_read(&g_in_flight) > 0 && tries < 1000000) {
        tries++;
    }
    return 0;
}

KPM_INIT(na_init);
KPM_CTL0(na_ctl0);
KPM_EXIT(na_exit);

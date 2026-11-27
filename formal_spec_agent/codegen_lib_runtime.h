/* Freestanding-friendly zero-copy runtime primitives for c99-lib-v1 generated libraries. */
#ifndef FSA_LIB_RUNTIME_H
#define FSA_LIB_RUNTIME_H

#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define FSA_SEQ_MOD INT64_C(4294967296)
#define FSA_SEQ_HALF INT64_C(2147483648)

enum fsa_kind {
    FSA_KIND_INT = 0,
    FSA_KIND_BOOL = 1,
    FSA_KIND_SEQ32 = 2,
    FSA_KIND_BYTES = 3,
    FSA_KIND_STRING = 4
};

enum fsa_err {
    FSA_OK = 0,
    FSA_ERR_OVERFLOW = 1,
    FSA_ERR_BYTE_CAP = 2,
    FSA_ERR_ARENA_CAP = 3,
    FSA_ERR_STRING_DOMAIN = 4,
    FSA_ERR_UNCOVERED = 5,
    FSA_ERR_CONFLICT = 6,
    FSA_ERR_INVARIANT = 7,
    FSA_ERR_TIMER_DELAY = 8,
    FSA_ERR_NONMONOTONIC = 9,
    FSA_ERR_TIMER_STEPS = 10,
    FSA_ERR_INVALID_ARG = 11,
    FSA_ERR_TEXT_CAP = 12
};

typedef struct {
    const uint8_t *ptr;
    uint16_t len;
} fsa_slice_t;

typedef struct {
    uint8_t *buf;
    uint32_t used;
    uint32_t cap;
} fsa_arena_t;

typedef struct {
    uint8_t kind;
    int64_t i64;
    fsa_slice_t bytes;
} fsa_val_t;

static inline fsa_val_t fsa_val_int(int64_t v) {
    fsa_val_t out;
    out.kind = FSA_KIND_INT;
    out.i64 = v;
    out.bytes.ptr = NULL;
    out.bytes.len = 0;
    return out;
}

static inline fsa_val_t fsa_val_bool(int v) {
    fsa_val_t out;
    out.kind = FSA_KIND_BOOL;
    out.i64 = v ? 1 : 0;
    out.bytes.ptr = NULL;
    out.bytes.len = 0;
    return out;
}

static inline fsa_val_t fsa_val_seq32(uint32_t v) {
    fsa_val_t out;
    out.kind = FSA_KIND_SEQ32;
    out.i64 = (int64_t)v;
    out.bytes.ptr = NULL;
    out.bytes.len = 0;
    return out;
}

static inline fsa_val_t fsa_val_bytes(const uint8_t *ptr, uint16_t len) {
    fsa_val_t out;
    out.kind = FSA_KIND_BYTES;
    out.i64 = 0;
    out.bytes.ptr = ptr;
    out.bytes.len = len;
    return out;
}

static inline fsa_val_t fsa_val_str(const char *utf8_ptr, uint16_t len) {
    fsa_val_t out;
    out.kind = FSA_KIND_STRING;
    out.i64 = -1;
    out.bytes.ptr = (const uint8_t *)utf8_ptr;
    out.bytes.len = len;
    return out;
}

static inline fsa_val_t fsa_val_str_id(int64_t id) {
    fsa_val_t out;
    out.kind = FSA_KIND_STRING;
    out.i64 = id;
    out.bytes.ptr = NULL;
    out.bytes.len = 0;
    return out;
}

static inline int64_t fsa_add(int64_t a, int64_t b, int *err) {
    if ((b > 0 && a > INT64_MAX - b) || (b < 0 && a < INT64_MIN - b)) {
        if (!*err) *err = FSA_ERR_OVERFLOW;
        return 0;
    }
    return a + b;
}

static inline int64_t fsa_sub(int64_t a, int64_t b, int *err) {
    if ((b > 0 && a < INT64_MIN + b) || (b < 0 && a > INT64_MAX + b)) {
        if (!*err) *err = FSA_ERR_OVERFLOW;
        return 0;
    }
    return a - b;
}

static inline int64_t fsa_mul(int64_t a, int64_t b, int *err) {
    if (a == 0 || b == 0) return 0;
    if ((a == -1 && b == INT64_MIN) || (b == -1 && a == INT64_MIN)) {
        if (!*err) *err = FSA_ERR_OVERFLOW;
        return 0;
    }
    if ((a > 0 && b > 0 && a > INT64_MAX / b) ||
        (a > 0 && b < 0 && b < INT64_MIN / a) ||
        (a < 0 && b > 0 && a < INT64_MIN / b) ||
        (a < 0 && b < 0 && a < INT64_MAX / b)) {
        if (!*err) *err = FSA_ERR_OVERFLOW;
        return 0;
    }
    return a * b;
}

static inline int64_t fsa_min(int64_t a, int64_t b) {
    return a < b ? a : b;
}

static inline int64_t fsa_seq_add(int64_t a, int64_t b) {
    int64_t rem = b % FSA_SEQ_MOD;
    if (rem < 0) rem += FSA_SEQ_MOD;
    uint64_t ua = (uint64_t)a & UINT64_C(0xFFFFFFFF);
    uint64_t ur = (uint64_t)rem;
    return (int64_t)((ua + ur) % UINT64_C(4294967296));
}

static inline int64_t fsa_seq_dist(int64_t a, int64_t b) {
    uint64_t ua = (uint64_t)a & UINT64_C(0xFFFFFFFF);
    uint64_t ub = (uint64_t)b & UINT64_C(0xFFFFFFFF);
    return (int64_t)((ub - ua) & UINT64_C(0xFFFFFFFF));
}

static inline int fsa_seq_lt(int64_t a, int64_t b) {
    int64_t d = fsa_seq_dist(a, b);
    return d > 0 && d < FSA_SEQ_HALF;
}

static inline int fsa_seq_le(int64_t a, int64_t b) {
    return fsa_seq_dist(a, b) < FSA_SEQ_HALF;
}

static inline int fsa_seq_comparable(int64_t a, int64_t b) {
    return fsa_seq_dist(a, b) != FSA_SEQ_HALF;
}

static inline fsa_slice_t fsa_slice_make(const uint8_t *ptr, uint16_t len) {
    fsa_slice_t s;
    s.ptr = ptr;
    s.len = len;
    return s;
}

static inline uint8_t *fsa_arena_alloc(fsa_arena_t *arena, size_t n, int *err) {
    if (n == 0) return arena ? arena->buf : NULL;
    if (!arena || !arena->buf || arena->used > arena->cap || n > (size_t)(arena->cap - arena->used)) {
        if (err && !*err) *err = FSA_ERR_ARENA_CAP;
        return NULL;
    }
    uint8_t *p = arena->buf + arena->used;
    arena->used += (uint32_t)n;
    return p;
}

static inline fsa_slice_t fsa_arena_copy(fsa_arena_t *arena, fsa_slice_t s, uint16_t byte_cap, int *err) {
    fsa_slice_t empty = {NULL, 0};
    if (s.len > byte_cap) {
        if (err && !*err) *err = FSA_ERR_BYTE_CAP;
        return empty;
    }
    if (s.len == 0) return empty;
    uint8_t *p = fsa_arena_alloc(arena, s.len, err);
    if (!p) return empty;
    memcpy(p, s.ptr, s.len);
    return fsa_slice_make(p, s.len);
}

static inline fsa_slice_t fsa_slice_sub(fsa_slice_t a, int64_t offset, int64_t count, uint16_t byte_cap, int *err) {
    fsa_slice_t empty = {NULL, 0};
    if (a.len > byte_cap) {
        if (err && !*err) *err = FSA_ERR_BYTE_CAP;
        return empty;
    }
    size_t start = offset < 0 ? 0U : ((uint64_t)offset > (uint64_t)a.len ? (size_t)a.len : (size_t)offset);
    size_t avail = (size_t)a.len - start;
    size_t n = count < 0 ? 0U : ((uint64_t)count > (uint64_t)avail ? avail : (size_t)count);
    return fsa_slice_make(n ? (a.ptr + start) : NULL, (uint16_t)n);
}

static inline int64_t fsa_slice_at_or_zero(fsa_slice_t a, int64_t offset, uint16_t byte_cap, int *err) {
    if (a.len > byte_cap) {
        if (err && !*err) *err = FSA_ERR_BYTE_CAP;
        return 0;
    }
    if (offset < 0 || (uint64_t)offset >= (uint64_t)a.len) return 0;
    return (int64_t)a.ptr[(size_t)offset];
}

static inline int fsa_slice_eq(fsa_slice_t a, fsa_slice_t b) {
    if (a.len != b.len) return 0;
    if (a.len == 0) return 1;
    return memcmp(a.ptr, b.ptr, a.len) == 0;
}

static inline fsa_slice_t fsa_concat(fsa_arena_t *arena, fsa_slice_t a, fsa_slice_t b, uint16_t byte_cap, int *err) {
    fsa_slice_t empty = {NULL, 0};
    if (a.len > byte_cap || b.len > byte_cap || b.len > byte_cap - a.len) {
        if (err && !*err) *err = FSA_ERR_BYTE_CAP;
        return empty;
    }
    uint16_t total = (uint16_t)(a.len + b.len);
    if (total == 0) return empty;
    uint8_t *p = fsa_arena_alloc(arena, total, err);
    if (!p) return empty;
    if (a.len) memcpy(p, a.ptr, a.len);
    if (b.len) memcpy(p + a.len, b.ptr, b.len);
    return fsa_slice_make(p, total);
}

static inline fsa_slice_t fsa_pack8(fsa_arena_t *arena, int64_t n, uint16_t byte_cap, int *err) {
    fsa_slice_t empty = {NULL, 0};
    if (byte_cap < 1) {
        if (err && !*err) *err = FSA_ERR_BYTE_CAP;
        return empty;
    }
    uint8_t *p = fsa_arena_alloc(arena, 1, err);
    if (!p) return empty;
    p[0] = (uint8_t)(n & 0xFF);
    return fsa_slice_make(p, 1);
}

static inline fsa_slice_t fsa_pack16be(fsa_arena_t *arena, int64_t n, uint16_t byte_cap, int *err) {
    fsa_slice_t empty = {NULL, 0};
    if (byte_cap < 2) {
        if (err && !*err) *err = FSA_ERR_BYTE_CAP;
        return empty;
    }
    uint8_t *p = fsa_arena_alloc(arena, 2, err);
    if (!p) return empty;
    uint16_t v = (uint16_t)n;
    p[0] = (uint8_t)(v >> 8);
    p[1] = (uint8_t)(v & 0xFF);
    return fsa_slice_make(p, 2);
}

static inline fsa_slice_t fsa_pack32be(fsa_arena_t *arena, int64_t n, uint16_t byte_cap, int *err) {
    fsa_slice_t empty = {NULL, 0};
    if (byte_cap < 4) {
        if (err && !*err) *err = FSA_ERR_BYTE_CAP;
        return empty;
    }
    uint8_t *p = fsa_arena_alloc(arena, 4, err);
    if (!p) return empty;
    uint32_t v = (uint32_t)n;
    p[0] = (uint8_t)(v >> 24);
    p[1] = (uint8_t)((v >> 16) & 0xFF);
    p[2] = (uint8_t)((v >> 8) & 0xFF);
    p[3] = (uint8_t)(v & 0xFF);
    return fsa_slice_make(p, 4);
}

static inline int64_t fsa_checksum16(fsa_slice_t a, uint16_t byte_cap, int *err) {
    if (a.len > byte_cap) {
        if (err && !*err) *err = FSA_ERR_BYTE_CAP;
        return 0;
    }
    uint64_t acc = 0;
    size_t i = 0;
    size_t alen = (size_t)a.len;
    const uint8_t *p = a.ptr;
    for (; i + 8U <= alen; i += 8U) {
        acc += (((uint64_t)p[i] << 8) | (uint64_t)p[i + 1U]) +
               (((uint64_t)p[i + 2U] << 8) | (uint64_t)p[i + 3U]) +
               (((uint64_t)p[i + 4U] << 8) | (uint64_t)p[i + 5U]) +
               (((uint64_t)p[i + 6U] << 8) | (uint64_t)p[i + 7U]);
    }
    for (; i + 1U < alen; i += 2U) {
        acc += ((uint64_t)p[i] << 8) | (uint64_t)p[i + 1U];
    }
    if (i < alen) {
        acc += ((uint64_t)p[i] << 8);
    }
    while (acc >> 16) {
        acc = (acc & UINT64_C(0xFFFF)) + (acc >> 16);
    }
    return (int64_t)(UINT64_C(0xFFFF) - acc);
}

static inline void fsa_buf_assign(uint8_t *dst, uint16_t *dst_len, uint16_t cap, fsa_slice_t src, int *err) {
    if (src.len > cap) {
        if (err && !*err) *err = FSA_ERR_BYTE_CAP;
        return;
    }
    if (src.len > 0 && !src.ptr) {
        if (err && !*err) *err = FSA_ERR_INVALID_ARG;
        return;
    }
    if (src.len) {
        memmove(dst, src.ptr, src.len);
    }
    *dst_len = src.len;
}

static inline int fsa_valid_utf8(const uint8_t *s, size_t n) {
    size_t i = 0;
    while (i < n) {
        uint8_t c = s[i];
        if (c < 0x80) { i++; continue; }
        int cont = 0;
        uint32_t cp = 0;
        if (c >= 0xC2 && c <= 0xDF) { cp = c & 0x1F; cont = 1; }
        else if (c >= 0xE0 && c <= 0xEF) { cp = c & 0x0F; cont = 2; }
        else if (c >= 0xF0 && c <= 0xF4) { cp = c & 0x07; cont = 3; }
        else return 0;
        if (i + (size_t)cont >= n) return 0;
        for (int j = 1; j <= cont; j++) {
            uint8_t cc = s[i + (size_t)j];
            if ((cc & 0xC0) != 0x80) return 0;
            cp = (cp << 6) | (cc & 0x3F);
        }
        if ((cont == 1 && cp < 0x80) ||
            (cont == 2 && cp < 0x800) ||
            (cont == 3 && cp < 0x10000) ||
            (cp >= 0xD800 && cp <= 0xDFFF) ||
            (cp > 0x10FFFF)) {
            return 0;
        }
        i += (size_t)cont + 1;
    }
    return 1;
}

#endif /* FSA_LIB_RUNTIME_H */

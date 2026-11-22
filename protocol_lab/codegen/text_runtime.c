/* Text pool for dynamic string event fields. Content-addressed bounded intern pool.
   Must be included after runtime.c which defines Buffer, failure, and helpers. */
#include <stdint.h>
#include <stddef.h>
#include <string.h>

typedef struct {
    int count;
    size_t len[TEXT_POOL_CAP];
    char data[TEXT_POOL_CAP][TEXT_CAP];
} TextPool;

static int hexval(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

static int valid_utf8(const char *s, size_t n) {
    size_t i = 0;
    while (i < n) {
        unsigned char c = (unsigned char)s[i];
        if (c < 0x80) { i++; continue; }
        int cont;
        uint32_t cp;
        if (c >= 0xC2 && c <= 0xDF) { cp = c & 0x1F; cont = 1; }
        else if (c >= 0xE0 && c <= 0xEF) { cp = c & 0x0F; cont = 2; }
        else if (c >= 0xF0 && c <= 0xF4) { cp = c & 0x07; cont = 3; }
        else return 0;
        if (i + cont >= n) return 0;
        for (int j = 1; j <= cont; j++) {
            unsigned char cc = (unsigned char)s[i + j];
            if ((cc & 0xC0) != 0x80) return 0;
            cp = (cp << 6) | (cc & 0x3F);
        }
        if ((cont == 1 && cp < 0x80) ||
            (cont == 2 && cp < 0x800) ||
            (cont == 3 && cp < 0x10000) ||
            (cp >= 0xD800 && cp <= 0xDFFF) ||
            (cp > 0x10FFFF)) return 0;
        i += cont + 1;
    }
    return 1;
}

static int text_find(TextPool *pool, const char *s, size_t n) {
    for (int i = 0; i < pool->count; i++)
        if (pool->len[i] == n && memcmp(pool->data[i], s, n) == 0)
            return i;
    return -1;
}

static int text_add(TextPool *pool, const char *s, size_t n) {
    int idx = text_find(pool, s, n);
    if (idx >= 0) return idx;
    if (n > TEXT_CAP || pool->count >= TEXT_POOL_CAP) return -1;
    memcpy(pool->data[pool->count], s, n);
    pool->len[pool->count] = n;
    pool->count++;
    return pool->count - 1;
}

static int parse_text(TextPool *pool, const char *token, int64_t *out) {
    if (!token || token[0] != 'u' || token[1] != ':') return 0;
    const char *hex = token + 2;
    size_t hexlen = strlen(hex);
    if (hexlen % 2 != 0) return 0;
    size_t n = hexlen / 2;
    if (n > TEXT_CAP) { failure = "text_capacity"; return 0; }
    char buf[TEXT_CAP];
    for (size_t i = 0; i < n; i++) {
        int hi = hexval(hex[2*i]);
        int lo = hexval(hex[2*i+1]);
        if (hi < 0 || lo < 0) return 0;
        buf[i] = (char)((hi << 4) | lo);
    }
    if (!valid_utf8(buf, n)) return 0;
    int idx = text_add(pool, buf, n);
    if (idx < 0) { failure = "text_capacity"; return 0; }
    *out = idx;
    return 1;
}

static void text_json(Buffer *out, TextPool *pool, int64_t id) {
    if (id < 0 || id >= pool->count) { failure = "text_id_out_of_range"; return; }
    size_t n = pool->len[id];
    const char *s = pool->data[id];
    text(out, "\"");
    for (size_t i = 0; i < n; i++) {
        unsigned char c = (unsigned char)s[i];
        if (c == '\"' || c == '\\') {
            text(out, c == '\"' ? "\\\"" : "\\\\");
        } else if (c < 0x20) {
            char esc[8];
            snprintf(esc, sizeof(esc), "\\u%04x", c);
            text(out, esc);
        } else {
            char one[2] = { (char)c, 0 };
            text(out, one);
        }
    }
    text(out, "\"");
}

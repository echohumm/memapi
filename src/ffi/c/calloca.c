#include <stddef.h>
#include <stdint.h>
#include <string.h>

#ifdef _MSC_VER
# include <malloc.h>
#endif
#ifndef _MSC_VER
# include <alloca.h>
#endif

// TODO: try to find some way to avoid stack overflow if too large
void c_alloca(
    const size_t size,
    const size_t align,
    const bool zero,
    void (*callback)(void*, uint8_t*, void*),
    void* closure,
    void* out
) {
    uint8_t *ptr;

    if (size == 0) {
        ptr = (uint8_t*)align;
    } else {
        // TODO: ideally we ignore user's alignment request if the platform's guaranteed align is >=
        size_t m1 = align - 1;
        size_t alloc_size = size + m1;
#ifdef _MSC_VER
        uint8_t *base = _alloca(alloc_size);
#else
        uint8_t *base = alloca(alloc_size);
#endif
        ptr = (uint8_t*)(((size_t)base + m1) & ~m1);
        if (zero) {
            memset(ptr, 0, size);
        }
    }

    // well, that was an annoying bug..
    callback(closure, ptr, out);
}

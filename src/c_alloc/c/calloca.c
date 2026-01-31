#include <stddef.h>
#include <stdint.h>

#ifdef _MSC_VER
# include <malloc.h>
#endif
#ifndef _MSC_VER
# include <alloca.h>
#endif

void c_alloca(
    size_t size,
    size_t align,
    void (*callback)(uint8_t*, void*, void*),
    void* closure,
    void* out
) {
    uint8_t *ptr;

    if (size == 0) {
        ptr = (uint8_t*)align;
    } else {
        size_t m1 = align - 1;
        size_t alloc_size = size + m1;
#ifdef _MSC_VER
        uint8_t *base = (uint8_t*)_alloca(alloc_size);
#else
        uint8_t *base = (uint8_t*)alloca(alloc_size);
#endif
        ptr = (uint8_t*)(((size_t)base + m1) & ~m1);
    }

    callback(ptr, closure, out);
}

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#if defined(_MSC_VER)
  #include <malloc.h>
#elif !defined(__MINGW64__)
  #include <alloca.h>
#endif

#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
  /* C11: use max_align_t */
  #include <stdalign.h>
  #include <stddef.h>
  #define GUARANTEED_ALIGN alignof(max_align_t)

#elif defined(__GNUC__) || defined(__clang__)
  /* GCC/Clang: try to use max_align_t if available, otherwise pick a wide alignment */
  #include <stddef.h>
  #if defined(__SIZEOF_MAX_ALIGN_T__)
    /* some targets expose max_align_t even in non-C11 modes */
    #define GUARANTEED_ALIGN __alignof__(max_align_t)
  #elif defined(__MINGW64__) || defined(__x86_64__) || defined(_M_X64) || defined(_M_AMD64)
    /* x86_64 targets: follow the 16-byte Windows / System V ABI */
    #define GUARANTEED_ALIGN 16
  #else
    /* conservative fallback, long double has large alignment */
    #define GUARANTEED_ALIGN __alignof__(long double)
  #endif

#elif defined(_MSC_VER)
  /* MSVC: x64 = 16, x86 = 8 (conservative) */
  #if defined(_M_X64) || defined(_M_AMD64)
    #define GUARANTEED_ALIGN 16
  #else
    #define GUARANTEED_ALIGN 8
  #endif

#else
  #define GUARANTEED_ALIGN 16
#endif



#if defined(_MSC_VER)
  #define ALLOCA(sz) _alloca(sz)
#else
  #define ALLOCA(sz) alloca(sz)
#endif

/* TODO: try to find some way to avoid stack overflow if too large */
void c_alloca(
    const size_t size,
    const size_t align,
    void (*callback)(void*, uint8_t*, void*),
    void* closure,
    void* out
) {
    /* determine whether we need extra space for padding */
    size_t alloc_size = size;
    size_t align_m_1;
    bool need_padding = (align > GUARANTEED_ALIGN);
    if (need_padding) {
        align_m_1 = align - 1;
        alloc_size += align_m_1;
    }

    /* allocate */
    uint8_t *ptr = (uint8_t*)ALLOCA(alloc_size);

    /* pad the pointer to be aligned */
    if (need_padding) {
        uintptr_t mask = (uintptr_t)(align_m_1);
        ptr = (uint8_t*)(((uintptr_t)ptr + mask) & ~mask);
    }

    callback(closure, ptr, out);
}

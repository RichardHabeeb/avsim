#pragma once
#include <stdint.h>


static inline uint32_t sub_until_zero(uint32_t a, uint32_t b) {
    return (b <= a) ? a - b : 0; 
}

static inline uint32_t max(int32_t a, int32_t b) {
    return (a > b) ? a : b;
}

static inline uint32_t min(int32_t a, int32_t b) {
    return (a < b) ? a : b;
}


static inline uint32_t sub_mod(uint32_t a, uint32_t b, uint32_t m) {
    return (a >= b) ? a - b : m - b + a;
}

static inline int32_t mod(int32_t x, int32_t m) {
    if (m < 0) m = -m;
    int r = x % m;
    return r < 0 ? r + m : r;
}
  
static inline int32_t modular_dist(int32_t a, int32_t b, int32_t m) {
    return min(mod(a - b, m), mod(b - a, m));
}

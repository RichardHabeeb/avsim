#pragma once
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct { double v; } radians_t;
typedef struct { double v; } meters_t;
typedef struct { int64_t v; } nanoseconds_t;
typedef struct { int64_t v; } pixels_t;

#define TEMPLATE_POINT_STRUCT(TYPE_NAME, TYPE) \
    typedef struct { \
        TYPE x; \
        TYPE y; \
    } TYPE_NAME;

TEMPLATE_POINT_STRUCT(point_meters_t, meters_t);
TEMPLATE_POINT_STRUCT(point_pixels_t, pixels_t);
TEMPLATE_POINT_STRUCT(point_int64_t, int64_t);

#undef TEMPLATE_POINT_STRUCT


typedef struct {
    point_meters_t midpoint;
    meters_t width;
    meters_t height;
} rect_meters_t;

typedef struct {
    point_pixels_t midpoint;
    pixels_t width;
    pixels_t height;
} rect_pixels_t;


#ifdef __cplusplus
} /* extern C */
#endif

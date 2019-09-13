#pragma once
#include <stdint.h>

extern "C" {

typedef struct { double v; } radians_t;
typedef struct { double v; } meters_t;
typedef struct { int64_t v; } nanoseconds_t;

typedef struct {
    meters_t x;
    meters_t y;
} point_meters_t;

typedef struct {
    int64_t x;
    int64_t y;
} point_int64_t;


typedef struct {
    point_meters_t midpoint;
    meters_t width;
    meters_t height;
} rect_meters_t;

typedef struct {
    point_int64_t midpoint;
    int64_t width;
    int64_t height;
} rect_int64_t;

}

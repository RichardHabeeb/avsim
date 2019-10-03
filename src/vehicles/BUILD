package(default_visibility = ["//visibility:public"])

cc_library(
	name = "simple_car",
	srcs = [
		"simple_car.c",
	],
	hdrs = [
		"simple_car.h",
	],
	deps = [
		"//src/common:common",
	]
)

cc_library(
    name = "vehicles",
    srcs = [
        "two_wheel.cpp",
        "two_wheel_damn.cpp",
    ],
    hdrs = [
        "vehicle.h",
        "two_wheel.h",
        "damn.h",
        "two_wheel_damn.h",
    ],
    deps = [
        "//src/common:common",
    ]
)

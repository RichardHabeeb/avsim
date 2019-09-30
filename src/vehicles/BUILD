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
    ],
    hdrs = [
        "vehicle.h",
        "two_wheel.h",
    ],
    deps = [
        "//src/common:common",
    ]
)

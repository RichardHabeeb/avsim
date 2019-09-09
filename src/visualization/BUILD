package(default_visibility = ["//visibility:public"])

cc_library(
	name = "vis2d",
	srcs = [
		"vis2d.cpp",
	],
	hdrs = [
		"visualization.h",
		"vis2d.h",
	],
	deps = [
		"//src/common:common",
		"//src/roads:roads",
		"//src/vehicles:simple_car",
		"//src/simulator:sim",
	],
	linkopts = [
		"-lSDL2",
		"-lSDL2_gfx",
	],
)

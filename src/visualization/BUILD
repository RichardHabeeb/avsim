package(default_visibility = ["//visibility:public"])

cc_library(
	name = "sdl_vis",
	srcs = [
		"draw.c",
	],
	hdrs = [
		"draw.h",
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

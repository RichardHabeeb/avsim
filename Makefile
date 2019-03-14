

CC=@gcc
LDFLAGS=-lSDL2 -lSDL2_gfx
CFLAGS=-Isrc -DDEBUG -Wall
OBJ_OUTPUT=avsim

BUILD_DIR=build

all:
	@echo "Building Simulator"
	@mkdir -p $(BUILD_DIR)
	$(CC) src/*.c $(CFLAGS) $(LDFLAGS) -o $(BUILD_DIR)/$(OBJ_OUTPUT)

clean:
	rm -rf $(BUILD_DIR)

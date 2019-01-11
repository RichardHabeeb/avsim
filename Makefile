

CC=@gcc
LDFLAGS=-lncurses
CFLAGS=-Isrc -DDEBUG -Wall

BUILD_DIR=build

all:
	@echo "Building Simulator"
	@mkdir -p $(BUILD_DIR)
	$(CC) src/*.c $(CFLAGS) $(LDFLAGS) -o $(BUILD_DIR)/avsim

clean:
	rm -rf $(BUILD_DIR)

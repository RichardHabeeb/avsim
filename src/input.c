#include <ncurses.h>
#include <stdint.h>

#include <input.h>

key_t pop_input_buf() {
    return getch();
}

void flush_input_buf() {
    while(getch() != ERR);
}

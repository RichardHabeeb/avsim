#pragma once
#include <ncurses.h>

#define key_t int
#define INPUT_BUF_EMPTY ERR

key_t pop_input_buf();
void flush_input_buf();

#include <ncurses.h>
#include <stdint.h>

#include <draw.h>
#include <pos.h>

#ifdef DEBUG
uint64_t frame_cnt;
#endif

pt32_t window_size;

void setup_draw() {
    initscr();
    noecho();
    curs_set(FALSE);

    getmaxyx(stdscr, window_size.y, window_size.x);

#ifdef DEBUG
    frame_cnt = 0;
#endif
}

void cleanup_draw() {
    endwin();
}

void draw() {
    clear();

#ifdef DEBUG
    mvprintw(window_size.y-1, 0, "window_size:(%u,%u); Frame:#%u", window_size.x, window_size.y, ++frame_cnt);
#endif

    refresh();
}


#include <ncurses.h>
#include <stdint.h>

#include <draw.h>
#include <pos.h>
#include <road.h>

#ifdef DEBUG
static uint64_t frame_cnt;
#endif

static pt32_t window_size;

void setup_draw() {
    initscr();
    noecho();
    nodelay(stdscr, TRUE);
    curs_set(FALSE);


#ifdef DEBUG
    frame_cnt = 0;
#endif
}

void cleanup_draw() {
    endwin();
}



static void draw_full_screen_road(road_t *road) {
    uint32_t road_top    = (window_size.y / 2)-(road->num_lanes);
    uint32_t road_bottom = (window_size.y / 2)+(road->num_lanes);
    uint32_t road_left   = (window_size.x / 2)-(road->length/2);
    uint32_t road_right  = (window_size.x / 2)+(road->length/2);
    for(uint32_t x = road_left; x <= road_right; x++) {
        mvprintw(road_top, x, "-");
        mvprintw(road_bottom, x, "-");
        if(x % 2 == 0) {
            for(uint32_t y = road_top+2; y < road_bottom; y+=2) {
                mvprintw(y, x, "-");
            }
        }
    }
}

void draw(road_t* roads) {
    clear();

    getmaxyx(stdscr, window_size.y, window_size.x);

    /* Single road drawing, for now */
    if(roads != NULL) {
        draw_full_screen_road(roads);
    }

#ifdef DEBUG
    mvprintw(window_size.y-1, 0, "window_size:(%u,%u); Frame:#%u", window_size.x, window_size.y, ++frame_cnt);
#endif

    refresh();
}


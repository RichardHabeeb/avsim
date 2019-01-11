#include <ncurses.h>
#include <stdint.h>

#include <draw.h>
#include <pos.h>
#include <road.h>

#ifdef DEBUG
static uint64_t frame_cnt;
#endif

static pt32_t window_size;

#define DEFAULT_COLOR 1
#define STRIPE_COLOR 2
#define CAR_COLOR 3

void setup_draw() {
    initscr();
    start_color();
    noecho();
    nodelay(stdscr, TRUE);
    curs_set(FALSE);
    init_pair(DEFAULT_COLOR, COLOR_WHITE, COLOR_BLACK);
    init_pair(STRIPE_COLOR, COLOR_YELLOW, COLOR_BLACK);
    init_pair(CAR_COLOR, COLOR_BLUE, COLOR_BLUE);

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
    uint32_t road_left   = 1;
    uint32_t road_right  = window_size.x-1;
    
    for(uint32_t x = road_left; x < road_right; x++) {
        attron(COLOR_PAIR(DEFAULT_COLOR));
        mvprintw(road_top, x, "-");
        mvprintw(road_bottom, x, "-");
        attron(COLOR_PAIR(STRIPE_COLOR));
        if(x % 2 == 0) {
            for(uint32_t y = road_top+2; y < road_bottom; y+=2) {
                mvprintw(y, x, "-");
            }
        }
    }
    uint32_t road_scale = road->length / (road_right-road_left);
    for(uint32_t i = 0; i < road->num_cars; i++) {
        attron(COLOR_PAIR(CAR_COLOR));
        car_t *car = &road->cars[i];
        for(uint32_t j = 0; j < car->length; j++) {
            mvprintw(road_top + car->lane*2 + 1, road_left + (car->pos/road_scale + j)%(road_right-road_left), " ");
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
    attron(COLOR_PAIR(DEFAULT_COLOR));
    mvprintw(window_size.y-1, 0, "window_size:(%u,%u); Frame:#%u", window_size.x, window_size.y, ++frame_cnt);
#endif

    refresh();
}


#include <stdint.h>
#include <ncurses.h>
#include <time.h>

#include <draw.h>
#include <input.h>
#include <road.h>

#define TICK_DURATION_NS 1000*1000*250

/* Single road, for now */
static road_t single_road;


static bool tick() {
    key_t in_key = pop_input_buf();
    while(in_key != INPUT_BUF_EMPTY) {
        if(in_key == 'q') {
            return FALSE;
        }
        in_key = pop_input_buf();
    }

    draw(&single_road);

    return TRUE;
}


int main(int argc, char* argv[]) {
    setup_draw();

    single_road.num_lanes = 8;
    single_road.length = 100;

    while(tick()) {
        nanosleep(&(const struct timespec){.tv_sec=0, .tv_nsec=TICK_DURATION_NS}, NULL);
    }

    cleanup_draw();
}


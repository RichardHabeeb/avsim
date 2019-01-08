#include <stdint.h>
#include <ncurses.h>
#include <time.h>

#include <draw.h>


#define TICK_DURATION_NS 1000*1000

void tick() {
    draw();
}


int main(int argc, char* argv[]) {
    setup_draw();

    for(int i=0; i<5000; i++) {
        tick();

        nanosleep(&(const struct timespec){.tv_sec=0, .tv_nsec=TICK_DURATION_NS}, NULL);
    }

    cleanup_draw();
}


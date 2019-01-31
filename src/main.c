#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <unistd.h>
#include <time.h>
#include <string.h>
#include <SDL2/SDL.h>

#include <config.h>
#include <draw.h>
#include <road.h>
#include <car.h>


static road_t single_road;
static car_t cars[CFG_NUM_CARS];

static bool paused = false;


static bool handle_events() {
    SDL_Event e;
    static bool left_mouse_down = false;
    static bool right_mouse_down = false;
    static bool middle_mouse_down = false;
    static SDL_Point prev_mouse_pos; 

    while(SDL_PollEvent(&e) != 0)
    {
        if(e.type == SDL_QUIT) return false;
        else if(e.type == SDL_KEYDOWN) {
            switch(e.key.keysym.sym) {
                case SDLK_q:
                case SDLK_ESCAPE:
                    return false;
                case SDLK_SPACE:
                    paused = !paused;
                    break;
                default:
                    break;
            }
        } else if(e.type == SDL_MOUSEBUTTONDOWN) {
            left_mouse_down   |= e.button.button == SDL_BUTTON_LEFT;
            right_mouse_down  |= e.button.button == SDL_BUTTON_RIGHT;
            middle_mouse_down |= e.button.button == SDL_BUTTON_MIDDLE;

        } else if(e.type == SDL_MOUSEBUTTONUP) {
            left_mouse_down   &= e.button.button == SDL_BUTTON_LEFT;
            right_mouse_down  &= e.button.button == SDL_BUTTON_RIGHT;
            middle_mouse_down &= e.button.button == SDL_BUTTON_MIDDLE;

        } else if(e.type == SDL_MOUSEMOTION) {
            if(right_mouse_down) {
                //get_draw_translation

            }

        } else if(e.type == SDL_MOUSEWHEEL) {
            SDL_Point s = get_draw_scale();
            if(e.wheel.y > 0) {
                s.x -= DRAW_SCALE_MAX/64;
                s.y -= DRAW_SCALE_MAX/64;
            } else {
                s.x += DRAW_SCALE_MAX/64;
                s.y += DRAW_SCALE_MAX/64;
            }
            set_draw_scale(s);
        }
    }
    return true;
}


static bool tick() {

    if(handle_events() == false) {
        return false;
    }

    if(paused) return true;

    road_tick(&single_road);

    draw(&single_road, 1);

    return true;
}

static void setup_single_road() {
    single_road.num_lanes = CFG_SINGLE_NUM_LANES;
    single_road.length = CFG_SINGLE_LEN_M * CFG_SPACE_SCALE;
    single_road.num_cars = CFG_NUM_CARS;
    single_road.cars = cars;
}

void setup_car_params(car_t * car, road_t * road) {
    memset(car, 0, sizeof(car_t));
    car->length  = (CFG_CAR_MIN_LEN_M      + rand()%(CFG_CAR_MAX_LEN_M - CFG_CAR_MIN_LEN_M))*CFG_SPACE_SCALE;
    car->top_spd = (CFG_CAR_MIN_TOP_SPD_MS + rand()%(CFG_CAR_MAX_TOP_SPD_MS - CFG_CAR_MIN_TOP_SPD_MS))*CFG_SPACE_SCALE;
    car->lane    = (rand()%road->num_lanes);
    car->front_sensor_range = CFG_CAR_FRONT_RANGE_M*CFG_SPACE_SCALE;
    car->rear_sensor_range = CFG_CAR_REAR_RANGE_M*CFG_SPACE_SCALE;
    car->side_sensor_range = CFG_CAR_SIDE_RANGE_LANES;
    car->top_acc = CFG_CAR_TOP_ACC*CFG_SPACE_SCALE;
    car->top_dec = CFG_CAR_TOP_DEC*CFG_SPACE_SCALE;
    
    do {
        car->pos = (rand()%road->length); //TODO abort on too many attempts
    } while(collision_check(road, car));
}


int main(int argc, char* argv[]) {
    srand(time(NULL));

#ifdef CFG_SINGLE_ROAD
    setup_single_road();

    for(uint32_t i = 0; i < CFG_NUM_CARS; i++) {
        setup_car_params(&single_road.cars[i], &single_road);
    }

    setup_draw(&single_road, 1);
#endif

    while(tick()) {
        usleep(CFG_TICK_SLP_US);
    }

    cleanup_draw();
}


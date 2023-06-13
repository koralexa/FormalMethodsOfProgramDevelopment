#include "map.h"
#include <stdlib.h>

int initializeMap(Map *map, int size) {
  map->items = malloc(size * sizeof(Item));

  if (map->items == NULL) {
    return 1;
  }

  map->capacity = size;
  map->count = 0;

  for (int i = 0; i < map->capacity; i++) {
    map->items[i].existent = 0;
  }

  return 0;
}

void finalizeMap(Map *map) {
  free(map->items);
  map->items = NULL;
}

int addElement(Map *map, Key *key, Value *value) {
  /*@
    loop invariant 0 <= i <= map->capacity;
    loop invariant is_valid_map(map);
    loop invariant \at(map->capacity, Pre) == map->capacity;
    loop invariant \at(map->count, Pre) == map->count;
    loop invariant map->count == all_count(map);

    loop assigns map->items[0..(map->capacity - 1)];

    loop variant map->capacity - i;
  */
  for (int i = 0; i < map->capacity; i++) {
    if (map->items[i].existent != 0 && map->items[i].key.a == key->a && map->items[i].key.b == key->b) {
      map->items[i].value = *value;
      return 1;
    }
  }

  if (map->count == map->capacity) {
    return 0;
  }

  /*@
    loop invariant 0 <= i <= map->capacity;
    loop invariant is_valid_map(map);
    loop invariant \at(map->capacity, Pre) == map->capacity;
    loop invariant map->count + 1 <= map->capacity;

    loop assigns map->items[0..(map->capacity - 1)];

    loop variant map->capacity - i;
  */
  for (int i = 0; i < map->capacity; i++) {
    if (map->items[i].existent == 0) {
      map->items[i].key = *key;
      map->items[i].value = *value;
      map->items[i].existent = 1;
      map->count = map->count + 1;
      return 1;
    }
  }

  return 0;
}

int removeElement(Map *map, Key *key, Value *value) {
  for (int i = 0; i < map->capacity; i++) {
    if (map->items[i].existent != 0 && map->items[i].key.a == key->a && map->items[i].key.b == key->b) {
      if (value != NULL) {
        *value = map->items[i].value;
      }
      map->items[i].existent = 0;
      map->count = map->count - 1;
      int last_idx = -1;
      for (int j = 0; j < map->capacity; j++) {
        if (map->items[j].existent != 0) {
          last_idx = j;
        }
      }
      if (last_idx < i) {
        return 1;
      } 
      map->items[i].key = map->items[last_idx].key;
      map->items[i].value = map->items[last_idx].value;
      map->items[i].existent = 1;
      map->items[last_idx].existent = 0;
      return 1;
    }
  }

  return 0;
}

int getElement(Map *map, Key *key, Value *value) {
  /*@
    loop invariant 0 <= i <= map->capacity;
    loop invariant is_valid_map(map);
    loop invariant \at(map->capacity, Pre) == map->capacity;
    loop invariant \at(map->count, Pre) == map->count;

    loop assigns \nothing;

    loop variant map->capacity - i;
  */
  for (int i = 0; i < map->capacity; i++) {
    if (map->items[i].existent != 0 && map->items[i].key.a == key->a && map->items[i].key.b == key->b) {
      *value = map->items[i].value;
      return 1;
    }
  }

  return 0;
}
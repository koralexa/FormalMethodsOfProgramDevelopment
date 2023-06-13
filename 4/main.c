#include "map.h"
#include <stdio.h>
#include <stdlib.h>

int test_is_empty() {
  Map *map = malloc(sizeof(Map));
  int res = initializeMap(map, 2);

  if (res != 0) {
    return 1;
  }

  if ((map->capacity != 2) || (map->count != 0)) {
    finalizeMap(map);
    free(map);
    return -1;
  }

  finalizeMap(map);
  free(map);
  return 0;
}

int test_add_element() {
  Map *map = malloc(sizeof(Map));
  int res = initializeMap(map, 2);

  if (res != 0) {
    return 1;
  }

  Key k;
  k.a = 1;
  k.b = 2;

  Value v;
  v.c = 3;
  v.d = 4;

  int add_res = addElement(map, &k, &v);

  if (add_res == 0 || map->count != 1) {
    finalizeMap(map);
    free(map);
    return -1;
  }

  finalizeMap(map);
  free(map);
  return 0;
}

int test_add_existing_element() {
  Map *map = malloc(sizeof(Map));
  int res = initializeMap(map, 2);

  if (res != 0) {
    return 1;
  }

  Key k;
  k.a = 1;
  k.b = 2;

  Value v1, v2, v3;
  v1.c = 3;
  v1.d = 4;
  v2.c = 5;
  v2.d = 6;

  int add_res1 = addElement(map, &k, &v1);
  int add_res2 = addElement(map, &k, &v2);
  int get_res = getElement(map, &k, &v3);

  if ((add_res1 == 0) || (get_res == 0)) {
    finalizeMap(map);
    free(map);
    return 1;
  }

  if ((add_res2 == 0) || (map->count != 1) || (v3.c != v2.c) || (v3.d != v2.d)) {
    finalizeMap(map);
    free(map);
    return -1;
  }

  finalizeMap(map);
  free(map);
  return 0;
}

int test_overflow() {
  Map *map = malloc(sizeof(Map));
  int res = initializeMap(map, 2);

  if (res != 0) {
    return 1;
  }

  Key k1, k2, k3;
  k1.a = 1;
  k1.b = 2;
  k2.a = 5;
  k2.b = 6;
  k3.a = 9;
  k3.b = 10;

  Value v;
  v.c = 3;
  v.d = 4;

  int add_res1 = addElement(map, &k1, &v);
  int add_res2 = addElement(map, &k2, &v);
  int add_res3 = addElement(map, &k3, &v);

  if (add_res1 == 0 || add_res2 == 0) {
    finalizeMap(map);
    free(map);
    return 1;
  }

  if ((add_res3 != 0) || (map->count != 2)) {
    finalizeMap(map);
    free(map);
    return -1;
  }

  finalizeMap(map);
  free(map);
  return 0;
}

int test_overflow_existing() {
  Map *map = malloc(sizeof(Map));
  int res = initializeMap(map, 2);

  if (res != 0) {
    return 1;
  }

  Key k1, k2, k3;
  k1.a = 1;
  k1.b = 2;
  k2.a = 5;
  k2.b = 6;
  k3.a = 1;
  k3.b = 2;

  Value v1, v2;
  v1.c = 3;
  v1.d = 4;
  v2.c = 7;
  v2.d = 8;

  int add_res1 = addElement(map, &k1, &v1);
  int add_res2 = addElement(map, &k2, &v1);
  int add_res3 = addElement(map, &k3, &v2);
  getElement(map, &k3, &v1);

  if (add_res1 == 0 || add_res2 == 0) {
    finalizeMap(map);
    free(map);
    return 1;
  }

  if ((add_res3 == 0) || (map->count != 2) || (v1.c != v2.c) || (v1.d != v2.d)) {
    finalizeMap(map);
    free(map);
    return -1;
  }

  finalizeMap(map);
  free(map);
  return 0;
}

int test_get_element() {
  Map *map = malloc(sizeof(Map));
  int res = initializeMap(map, 2);

  if (res != 0) {
    return 1;
  }

  Key k;
  k.a = 1;
  k.b = 2;

  Value v1, v2;
  v1.c = 3;
  v1.d = 4;

  int add_res = addElement(map, &k, &v1);

  if (add_res == 0) {
    finalizeMap(map);
    free(map);
    return 1;
  }

  int get_res = getElement(map, &k, &v2);

  if ((get_res == 0) || (v2.c != v1.c) || (v2.d != v1.d)) {
    finalizeMap(map);
    free(map);
    return -1;
  }

  finalizeMap(map);
  free(map);
  return 0;
}

int test_get_not_existing_element() {
  Map *map = malloc(sizeof(Map));
  int res = initializeMap(map, 2);

  if (res != 0) {
    return 1;
  }

  Key k;
  k.a = 1;
  k.b = 2;

  Value v;
  v.c = -1;
  v.d = -1;

  int get_res = getElement(map, &k, &v);

  if ((get_res != 0) || (v.c != -1) || (v.d != -1)) {
    finalizeMap(map);
    free(map);
    return -1;
  }

  finalizeMap(map);
  free(map);
  return 0;
}

int test_remove_element() {
  Map *map = malloc(sizeof(Map));
  int res = initializeMap(map, 2);

  if (res != 0) {
    return 1;
  }

  Key k1, k2;
  k1.a = 1;
  k1.b = 2;
  k2.a = 5;
  k2.b = 6;


  Value v1, v2;
  v1.c = 3;
  v1.d = 4;

  int add_res1 = addElement(map, &k1, &v1);
  int add_res2 = addElement(map, &k2, &v1);

  if (add_res1 == 0 || add_res2 == 0) {
    finalizeMap(map);
    free(map);
    return 1;
  }

  int remove_res = removeElement(map, &k1, &v2);

  if ((remove_res == 0) || (v2.c != v1.c) || (v2.d != v1.d) || (map->count != 1)) {
    finalizeMap(map);
    free(map);
    return -1;
  }

  finalizeMap(map);
  free(map);

  return 0;
}

int test_remove_not_existing_element() {
  Map *map = malloc(sizeof(Map));
  int res = initializeMap(map, 2);

  if (res != 0) {
    return 1;
  }

  Key k;
  k.a = 1;
  k.b = 2;

  Value v;
  v.c = -1;
  v.d = -1;

  int remove_res = removeElement(map, &k, &v);

  if ((remove_res != 0) || (v.c != -1) || (v.d != -1) || (map->count != 0)) {
    finalizeMap(map);
    free(map);
    return -1;
  }

  finalizeMap(map);
  free(map);
  return 0;
}

int main() {
  int t1 = test_is_empty();
  int t2 = test_add_element();
  int t3 = test_add_existing_element();
  int t4 = test_overflow();
  int t5 = test_overflow_existing();
  int t6 = test_get_element();
  int t7 = test_get_not_existing_element();
  int t8 = test_remove_element();
  int t9 = test_remove_not_existing_element();

  printf("%d %d %d %d %d %d %d %d %d\n", t1, t2, t3, t4, t5, t6, t7, t8, t9);

  return 0;
}
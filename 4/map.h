#ifndef __MAP_H__
#define __MAP_H__

#include "maptypes.h"

/*@ 
  axiomatic ItemsCount {
    logic integer count{L} (Map *map, integer m, integer n);

    axiom count_zero: 
      \forall Map *map, integer m, n; (m >= n) ==> (count(map, m, n) == 0);

    predicate count_one_p{L} (Map *map, integer m) =
      count(map, m, m + 1) == (map->items[m].existent ? 1 : 0);

    axiom count_one{L}: 
      \forall Map *map, integer m; count_one_p(map, m);

    predicate count_split_p{L} (Map *map, integer m, integer n, integer k) =
      count(map, m, k) == count(map, m, n) + count(map, n, k);

    axiom count_split{L}: 
      \forall Map *map, integer m, n, k; 
      (m <= n <= k) ==> count_split_p(map, m, n, k);
  }
*/

/*@ logic integer all_count(Map *map) = count(map, 0, map->capacity); */

/*@
  // Структура может хранить лишь единственное отображение для конкретного ключа.
  // Никакие операции над структурой данных не должны приводить ее в такое состояние, чтобы после этого добавление одного 
  // отображения увеличило количество отображений более, чем на 1. Иными словами, в структуре данных, все existent элементы 
  // массива должны означать отображения из хэш-таблицы.
  predicate unique_items (Map *map) = 
    (\forall integer i; 
      (0 <= i < map->capacity) && (map->items[i].existent != 0) 
      ==> 
      (\forall integer j; (j != i) && (map->items[j].existent != 0) ==> (map->items[i].key != map->items[j].key)));

  // Его (Items) поле existent может быть истиной (то есть равняться единице) или ложью (то есть равняться нулю).
  predicate zero_or_one_existent (Map *map) =
    \forall integer i; (0 <= i <= map->capacity) ==> (i == 0 || i == 1);

  // Поле items структуры Map представляет собой массив длины capacity.
  predicate valid_items (Map *map) = 
    (map->capacity > 0) && (0 <= map->count <= map->capacity) && \valid(map->items + (0..map->capacity - 1));

  // Поле count этой структуры определяет, сколько элементов данного массива имеет поле existent установленным в истину (единицу).
  predicate count_correct (Map *map) = 
    (all_count(map) == map->count);

  // за двумя последовательно идущими элементами, у которых existent установлен в ложь, остальные элементы тоже имеют existent установленным в ложь.
  predicate not_existent_tail (Map *map) = 
    (\forall integer i; 
      (i < map->capacity - 1) && (map->items[i].existent == 0) && (map->items[i + 1].existent == 0)
      ==> 
      (\forall integer j; (i + 1 < j < map->capacity) ==> map->items[j].existent == 0));

  predicate is_valid_map (Map *map) = 
    \valid(map) && 
    unique_items(map) &&
    zero_or_one_existent(map) &&
    valid_items(map) &&
    count_correct(map) &&
    not_existent_tail(map);

  predicate is_empty_map (Map *map) = 
    (map->count == 0) &&
    (\forall integer i; (0 <= i < map->capacity) ==> map->items[i].existent == 0);

  predicate full{L} (Map *map) = (map->capacity == map->count);

  predicate has_key{L} (Map *map, Key *key) =
    \exists integer i; 
      (0 <= i < map->capacity) && 
      (map->items[i].existent != 0) &&
      (map->items[i].key == *key);

  predicate has_item{L1, L2} (Map *map, Key *key, Value *value) =
    \exists integer i; 
      (0 <= i < \at(map->capacity, L1)) && 
      (\at(map->items[i].existent, L1) != 0) &&
      (\at(map->items[i].key, L1) == \at(*key, L2)) &&
      (\at(map->items[i].value, L1) == \at(*value, L2));

  predicate has_place_for_item{L} (Map *map, Key *key) =
    !full(map) || has_key(map, key);

*/


int initializeMap(Map *map, int size);

/*@
  requires is_valid_map(map); // На вход функции должен подаваться указатель на область памяти, проинициализированную функцией initializeMap()
  requires \freeable(map->items); // На вход функции должен подаваться указатель на область памяти, проинициализированную функцией initializeMap()

  frees map->items; // освобождает динамическую память, используемую для ассоциативного массива map

  ensures \allocable(map->items); // освобождает динамическую память, используемую для ассоциативного массива map
*/
void finalizeMap(Map *map);


/*@
  requires is_valid_map(map);
  requires \valid(map);
  requires \valid(key);
  requires \valid(value);

  allocates \nothing; // Ничего другого функция не делает.
  frees \nothing; // Ничего другого функция не делает.
  assigns map->count; // добавляет отображение заданного ключа key на заданное значение value
  assigns map->items[0..map->capacity - 1]; // Функция имеет право изменять структуру ассоциативного массива, если это не отражается на содержащихся в нём парах.

  // Ничего другого функция не делает, требования к типу данных
  ensures is_valid_map(map);

  // Функция добавляет в заданный ассоциативный массив map отображение заданного ключа key на заданное значение value и 
  // возвращает истину (единицу), если в нём было место для этого отображения.
  ensures 
    has_place_for_item{Pre}(map, key) 
    ==> 
    (\result == 1) && has_item{Here, Here}(map, key, value) && (map->count == \at(map->count, Pre) + (has_key{Pre}(map, key) ? 0 : 1)); 

  // Если в ассоциативном массиве было недостаточно места, функция возвращает ложь (ноль)
  ensures !has_place_for_item{Pre}(map, key) ==> (\result == 0);

  // Функция не меняет переданные ключ и значение
  ensures \at(*key, Pre) == *key && \at(*value, Pre) == *value;

  // Функция не добавляет другие отображения, кроме отображения по заданному ключу, если оно было.
  ensures \forall integer i;
    ((0 <= i < map->capacity) && (map->items[i].existent != 0) && (map->items[i].key != *key))
    ==>
    (has_item{Pre, Here}(map, &map->items[i].key, &map->items[i].value));

  // Функция не удаляет другие отображения, кроме отображения по заданному ключу, если оно было.
  ensures \forall integer i;
    ((0 <= i < map->capacity) && (\at(map->items[i].existent, Pre) != 0) && (\at(map->items[i].key, Pre) != *key))
    ==>
    (has_item{Here, Pre}(map, &map->items[i].key, &map->items[i].value));

*/
int addElement(Map *map, Key *key, Value *value);


int removeElement(Map *map, Key *key, Value *value);

/*@
  requires is_valid_map(map);
  requires \valid(map);
  requires \valid(key);
  requires \valid(value);

  allocates \nothing; // Ничего другого функция не делает.
  frees \nothing; // Ничего другого функция не делает.
  assigns *value; // возвращает по указателю value сохранённое в ассоциативном массиве map значение для заданного ключа key

  // Функция getElement() возвращает по указателю value сохранённое в ассоциативном массиве map значение для заданного 
  // ключа key и возвращает истину (единицу), если заданный ассоциативный массив имеет отображения для заданного ключа.
  ensures has_key{Pre}(map, key) ==> (\result == 1) && has_item{Pre, Pre}(map, key, value);

  // В случае, если значение по заданному ключу не содержится в отображении, возвращается ложь (ноль) и ничего другого не происходит.
  ensures !has_key{Pre}(map, key) ==> (\result == 0) && (*value == \at(*value, Pre));

  // Функция не меняет ассоциативный массив
  ensures \at(map->capacity, Pre) == map->capacity;
  ensures \at(map->count, Pre) == map->count;
  ensures 
    \forall integer i;
      (0 <= i < map->capacity)
      ==>
      ((map->items[i].existent == \at(map->items[i].existent, Pre)) && 
      (map->items[i].key.a == \at(map->items[i].key.a, Pre)) &&
      (map->items[i].key.b == \at(map->items[i].key.b, Pre)) &&
      (map->items[i].value.c == \at(map->items[i].value.c, Pre)) &&
      (map->items[i].value.d == \at(map->items[i].value.d, Pre)));

  // и переданный ключ.
  ensures *key == \at(*key, Pre); 

  // Функция не меняет ассоциативный массив, ничего другого функция не делает, требования к типу данных
  ensures is_valid_map(map);
*/
int getElement(Map *map, Key *key, Value *value);

#endif // __MAP_H__
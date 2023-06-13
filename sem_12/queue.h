struct Queue {
  int *array;
  int capacity;
  int curr_elem;
  int empty_elem;
};

/*@
  predicate is_valid_queue (struct Queue *self) = 
    \valid(self) && self->capacity > 1 && \valid(self->array + (0..self->capacity  - 1)) && 
    0 <= self->curr_elem < self->capacity && 0 <= self->empty_elem < self->capacity;

  predicate is_empty_queue (struct Queue * self) = self->curr_elem == self->empty_elem;

  predicate same_items{L1, L2} (struct Queue *self, integer begin, integer size) = \forall integer k;
*/

/*@
  requires \valid(self);
  requires max_size > 0;

  assigns *self;

// allocates \nothing -- ничего не аллоцирует
  allocates self->array;

//  ensures \result == 0 ==> \offset_min(self->array) == 0; (это то же что freeable)
  ensures \result == 0 ==> \freeable(self->array);
//  ensures \result == 0 ==> \offset_min{Pre}(self->array, Pre) > \offset_max{Pre}(self->array); (это то же что allocable)
  ensures \result == 0 ==> \allocable{Pre}(self->array);
  ensures \result == 0 ==> is_valid_queue(self);
  ensures \result == 0 ==> is_empty_queue(self); 
  ensures \result == 0 ==> self->capacity == max_size + 1;
*/

int q_init(struct Queue * self, int max_size);

void q_clear(struct Queue * self);

int q_add(struct Queue *self, int elem);

int q_remove(struct Queue *self, int *elem);

int q_is_empty(struct Queue *self);
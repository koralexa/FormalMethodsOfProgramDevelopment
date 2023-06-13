/*@
  @ requires a >= 0;
  @ requires b > 0;
  @ requires \valid(d);
  @ requires \valid(r);
  @ requires (\base_addr(d) == \base_addr(r)) ==> (d != r);
  @ assigns *d, *r;
  @ ensures a == *d * b + *r;
  @ ensures 0 <= *r < b;
*/

void div(int a, int b, int * d, int * r) {
  int d_p = 0;
  /*@
    @ loop invariant a >= 0;
    @ loop invariant \at(a, Pre) == d_p * b + a;
    @ loop variant a;
  */
  while (a >= b) {
    a = a - b;
    d_p++;
  }
  *d = d_p;
  *r = a;
}

int main(void) {
  int pp[3];
  pp[2] = 42;
  div(10, 2, pp, pp + 1);
  //@ assert (pp[0] == 5) && (pp[1] == 0);
  //@ assert pp[2] == 42;
}

// Доступно:
// \valid(p)
// \valid(p + (n..m))
// \offset_min(p)
// \offset_max(p)
// \base_addr(p) == \base_addr(q) - находятся в одном блоке
// *p - как для указателей в С
// p[i]
// p + i
// p - q
// p < q
// ||
// &&
// ! - отрицание
// ==> - импликация
// <==> - эквивалентность
// \forall <тип> <параметр>, [,<тип> <параметр>];
// \exists <тип> <параметр> [,<тип> <параметр>];
// int - ограниченные целые числа (как в С)
// integer - все целые числа
// \old(<выражение>) - как old в WhyML
// \at(<выражение>, <метка>) - как at в WhyML

// Стандартрные метки:
// Pre - в самом начале (при вызове)
// Here - прямо сейчас
// Post - при возврате

// !!! *\old(p) не нужно путать с \old(*p)

// assigns - вся память этих блоков за исключением того, что указали, не меняется
// allocates - то же самое, только с alloc_table
// frees - то же самое, что allocates, только используется метка Pre (у allocates используется Post)

// язык называется ACSL
// документация на сайте прака

// запуск: frama-c -av <путь> [<путь>]
// -av -  подгрузить плагин astraver
/***************************************
Этот модуль описывает типы данных для представления
ориентированных графов, их вершин и дуг.

Граф представлен в типе `Graph`.

Поле `vertices` описывает вершины графа. Это массив из `vsize` значений
типа `Vertex`. Тип `Vertex` описывает размещение некоторой вершины графа
в массиве `vertices`. Поле `existent` в элементе массива `vertices` с
некоторым индексом `i` равно истине (т.е. не равно 0) тогда, когда в этом
элементе размещена вершина графа. В противном случае элемент массива
`vertices` с индексом `i` считается свободным.

Поле `edges` описывает дуги графа. Это массив из `esize` значений типа `Edge`.
Тип `Edge` описывает размещение некоторой дуги графа в массиве `edges`.
Поле `existent` в элементе массива `edges` имеет тот же смысл, что и то же
поле в элементе массива `vertices`. Поля `from` и `to` должны быть индексами в
массиве `vertices` и означают вершины, из которой исходит дуга и в которую
входит дуга.

Поле `ecnt` означает то количество первых элементов массива `edges`,
после которого все остальные элементы будут свободными.

Ниже приведено определение описанных типов и предикат `valid`, формально
описывающий инвариант типа `Graph`.

В конце модуля размещена функция `add_edge`, которая добавляет дугу в граф.
Ее аргумент `g` означает граф, в который надо
добавить дугу, аргументы `f` и `t` означают индексы в массиве `g->vertices`,
означающие начало и конец добавляемой дуги. Функция применима только
к графам, в которых есть свободное место для добавления дуги.
Перед функцией размещена ее формальная спецификация на языке `ACSL`.
****************************************/


typedef struct {
    int payload;
    int existent;
} Vertex;

typedef struct {
	int from;
	int to;
	int existent;
} Edge;

typedef struct {
	Vertex *vertices;
	int vsize;
	Edge *edges;
	int ecnt;
	int esize;
} Graph;

/*@
  predicate is_vertex(Graph *g, integer v) =
  	0 <= v < g->vsize;

  predicate edge_valid(Graph *g, integer k) =
 	g->edges[k].existent ==>
	is_vertex(g, g->edges[k].from) &&
	is_vertex(g, g->edges[k].to) &&
	g->vertices[g->edges[k].from].existent &&
	g->vertices[g->edges[k].to].existent;

  predicate edges_valid(Graph *g, integer n) =
 	\forall integer k; 0 <= k < n ==> edge_valid(g, k);

  predicate graph_valid(Graph *g) =
 	g->vsize > 0 &&
    g->esize > 0 &&
    g->esize >= g->ecnt >= 0 &&
	\valid(g->vertices + (0 .. g->vsize - 1)) &&
	\valid(g->edges + (0 .. g->esize - 1)) &&
	edges_valid(g, g->ecnt) &&
	(\forall integer k; g->ecnt <= k < g->esize ==> !g->edges[k].existent);
*/

/*@ predicate full(Graph *g) = range_existent(g, 0, g->esize);
    predicate range_existent(Graph *g, integer m, integer n) = \forall integer k; m <= k < n ==> g->edges[k].existent;
*/

/*@ axiomatic EdgesCount {
    logic integer count{L}(Graph *g, integer f, integer t, integer m, integer n);

    axiom count_zero: \forall Graph *g, integer f, t, m, n; m >= n ==>
        count(g, f, t, m, n) == 0;

	predicate count_one_p{L}(Graph *g, integer f, integer t, integer m) =
        count(g, f, t, m, m + 1) == (g->edges[m].existent && g->edges[m].from == f && g->edges[m].to == t ? 1 : 0);

    axiom count_one{L}: \forall Graph *g, integer f, t, m; count_one_p(g, f, t, m);

    predicate count_split_p{L}(Graph *g, integer f, integer t, integer m, integer n, integer k) =
        count(g, f, t, m, k) == count(g, f, t, m, n) + count(g, f, t, n, k);

    axiom count_split{L}: \forall Graph *g, integer f, t, m, n, k; m <= n <= k ==>
        count_split_p(g, f, t, m, n, k);
}*/

/*@ logic integer all_count(Graph *g, integer f, integer t) = count(g, f, t, 0, g->esize); */

/*@
    lemma count_zero_lemma{L}:
        \forall Graph *g, integer f, t, m, n; 
            (m >= n) ==> (count(g, f, t, m, n) == 0);

    lemma count_one_lemma{L}:
        \forall Graph *g, integer f, t, m; 
            count_one_p(g, f, t, m) && 
            (count(g, f, t, m, (m + 1)) == (g->edges[m].existent != 0 && g->edges[m].from == f && g->edges[m].to == t ? 1 : 0));

    lemma count_split_lemma{L}: 
        \forall Graph *g, integer f, t, m, n, k; 
            (m <= n <= k) 
            ==> 
            count_split_p(g, f, t, m, n, k) && 
            (count(g, f, t, m, k) == count(g, f, t, m, n) + count(g, f, t, n, k));

    lemma count_split_2_lemma{L}:
        \forall Graph *g, integer f, t, m, n; 
            (m <= n) 
            ==> 
            count(g, f, t, m, (n + 1)) == count(g, f, t, m, n) + count(g, f, t, n, (n + 1));  

    lemma count_double_split_lemma{L}:
        \forall Graph *g, integer f, t, m, n, k; 
            (m <= k <= n - 1) 
            ==> 
            (count(g, f, t, m, n) == count(g, f, t, m, k) + count(g, f, t, k, (k + 1)) + count(g, f, t, (k + 1), n));

    lemma all_count_lemma{L}: 
        \forall Graph *g, integer k, f, t;
            (0 <= g->ecnt <= g->esize) 
            ==> 
            (all_count(g, f, t) == count(g, f, t, 0, g->esize)) &&
            (all_count(g, f, t) == count(g, f, t, 0, g->ecnt) + count(g, f, t, g->ecnt, g->esize)) &&
            (count(g, f, t, 0, g->esize) == count(g, f, t, 0, g->ecnt) + count(g, f, t, g->ecnt, g->esize));

    lemma zero_after_ecnt_lemma{L}: 
        \forall Graph *g, integer f, t, m;
            graph_valid(g) ==> 
            (g->ecnt <= (m - 1) < g->esize) ==> 
            (count(g, f, t, (m - 1), m) == 0) && (g->edges[m - 1].existent == 0);

    lemma count_lemma{L}: 
        \forall Graph *g, integer f, t, m;
            (0 <= (m - 1) <= g->ecnt) ==> 
            (count(g,f, t, 0, m) == count(g, f, t, 0, (m - 1)) + count(g, f, t, (m - 1), m));

*/

/*@
    ghost
    /@
        lemma
        requires \valid(g);
        requires graph_valid(g);
        requires g->ecnt <= k <= g->esize;
        decreases k - g->ecnt;
        ensures count(g, f, t, g->ecnt, k) == 0;
    @/
    void count_not_existent_lemma(Graph *g, int f, int t, int k) {
        if (k > g->ecnt) {
            //@ assert count(g, f, t, (k - 1), k) == 0;
            //@ assert count(g, f, t, g->ecnt, k) == count(g, f, t, g->ecnt, (k - 1)) + count(g, f, t, (k - 1), k); 
            count_not_existent_lemma(g, f, t, (k - 1));
        }
    }
        
*/

/*@
    requires \valid(g) && graph_valid(g);
    requires is_vertex(g, f);
    requires is_vertex(g, t);
    requires g->vertices[f].existent;
    requires g->vertices[t].existent;

    assigns \nothing;

    ensures \result == all_count(g, f, t);
*/
int
count(Graph *g, int f, int t)
{
    int c = 0;
    /*@
        loop invariant i >= 0;
        loop invariant i <= g->ecnt;
        loop invariant c == count(g, f, t, 0, i);
        loop invariant (i < g->ecnt) ==> \valid(g->edges + (0..i));
        loop invariant (0 <= i <= g->ecnt);
        loop invariant (0 <= c <= i);

        loop variant g->ecnt - i;
    */
    for (int i = 0; i < g->ecnt; ++i) {
        if (g->edges[i].existent && g->edges[i].from == f && g->edges[i].to == t) {
            /*@
                assert count(g, f, t, i, (i + 1)) == 1;
            */
            ++ c;
        } else {
            /*@
                assert count(g, f, t, i, (i + 1)) == 0;
            */
        }
    }
    /*@
        assert count(g, f, t, 0, g->ecnt) == c;
    */
    /*@
        assert count(g, f, t, g->ecnt, g->esize) == 0;
    */
    /*@
        assert count(g, f, t, 0, g->ecnt) + count(g, f, t, g->ecnt, g->esize) == count(g, f, t, 0, g->esize);
    */
    /*@
        assert count(g, f, t, 0, g->ecnt) == count(g, f, t, 0, g->esize);
    */
    /*@
        assert count(g, f, t, 0, g->esize) == all_count(g, f, t);
    */
    /*@
        assert all_count(g, f, t) == c;
    */
    return c;
}

/*@
  requires \valid(g) && graph_valid(g);
  requires is_vertex(g, f);
  requires is_vertex(g, t);
  requires g->vertices[f].existent;
  requires g->vertices[t].existent;
  requires !full(g);
  ensures graph_valid(g);
  ensures all_count(g, f, t) == all_count{Pre}(g, f, t) + 1;
  ensures \forall integer f2, t2; (f2 != f || t2 != t) ==> all_count(g, f2, t2) == all_count{Pre}(g, f2, t2);
*/
void
add_edge(Graph *g, int f, int t)
{
    if (g->ecnt < g->esize) {
        
        g->edges[g->ecnt].from = f;
        g->edges[g->ecnt].to = t;
        g->edges[g->ecnt].existent = 1;
	    ++ g->ecnt;
        /*@ 
            ghost
            int i = 0;
            /@
                loop invariant i >= 0;
                loop invariant i <= g->esize;
                loop invariant graph_valid(g);
                loop invariant (i < g->ecnt) ==> count{Here}(g, f, t, 0, i) == count{Pre}(g, f, t, 0, i);
                loop invariant (i >= g->ecnt) ==> count{Here}(g, f, t, 0, i) == (count{Pre}(g, f, t, 0, i) + 1);
                loop invariant \forall integer k; 
                    (0 <= k <= i) && (k < g->esize) ==> 
                    (k != (g->ecnt - 1)) ==> 
                    (\at(g->edges[k].from, Pre) == \at(g->edges[k].from, Here)) &&
                    (\at(g->edges[k].to, Pre) == \at(g->edges[k].to, Here)) &&
                    (\at(g->edges[k].existent, Pre) == \at(g->edges[k].existent, Here));
                loop invariant \forall integer k;
                    (0 <= k < i) && (k != g->ecnt - 1)
                    ==>
                    (count{Pre}(g, f, t, k, (k + 1)) == count{Here}(g, f, t, k, (k + 1)));
                loop invariant (i < g->esize) ==> \valid(g->edges + (0..i));
                loop invariant \forall integer f2, t2;
                    (i < g->ecnt - 1)
                    ==> 
                    (count{Pre}(g, f2, t2, 0, (i + 1)) == count{Pre}(g, f2, t2, 0, i) + count{Pre}(g, f2, t2, i, (i + 1)));
                loop invariant \forall integer f2, t2;
                    (g->ecnt - 1 <= i < g->esize)
                    ==> 
                    (count{Pre}(g, f2, t2, 0, (i + 1)) == count{Pre}(g, f2, t2, 0, i) + count{Pre}(g, f2, t2, i, (i + 1)));
                loop invariant \forall integer f2, t2;
                    (g->ecnt - 1 <= i < g->esize)
                    ==> 
                    (count{Here}(g, f2, t2, 0, (i + 1)) == count{Here}(g, f2, t2, 0, i) + count{Here}(g, f2, t2, i, (i + 1)));
                loop invariant \forall integer k;
                    (0 <= k < g->esize) ==>
                        \forall integer f2, t2;
                            (f2 != f || t2 != t) ==>(count{Pre}(g, f2, t2, 0, (k + 1)) == count{Pre}(g, f2, t2, 0, k) + count{Pre}(g, f2, t2, k, (k + 1)));
                loop invariant \forall integer k;
                    (0 <= k < g->esize) ==>
                        \forall integer f2, t2;
                            (f2 != f || t2 != t) ==> (count{Here}(g, f2, t2, 0, (k + 1)) == count{Here}(g, f2, t2, 0, k) + count{Here}(g, f2, t2, k, (k + 1)));
                loop invariant \forall integer k;
                    (0 <= k <= i - 1) ==>
                        \forall integer f2, t2;
                            (f2 != f || t2 != t) ==> (count{Here}(g, f2, t2, k, (k + 1)) == count{Pre}(g, f2, t2, k, (k + 1)));
                loop invariant \forall integer k; 
                    (0 <= k <= i)
                    ==>
                    \forall integer f2, t2;
                        (f2 != f || t2 != t) ==> count{Here}(g, f2, t2, 0, k) == count{Pre}(g, f2, t2, 0, k);

                loop variant g->esize - i;
            @/
            while (i < g->esize) {
                i++;
            }
        */
        
        /*@ 
            assert \forall integer f2, t2; 
                (f2 != f || t2 != t) ==> (count{Here}(g, f2, t2, (i - 1), i) ==  count{Pre}(g, f2, t2, (i - 1), i));
        */
        /*@ 
            assert \forall integer f2, t2; 
                (f2 != f || t2 != t) ==> (count{Here}(g, f2, t2, 0, i) ==  count{Here}(g, f2, t2, 0, (i - 1)) + count{Here}(g, f2, t2, (i - 1), i));
        */
        /*@ 
            assert \forall integer f2, t2; 
                (f2 != f || t2 != t) ==> (count{Pre}(g, f2, t2, 0, i) ==  count{Pre}(g, f2, t2, 0, (i - 1)) + count{Pre}(g, f2, t2, (i - 1), i));
        */
        /*@ 
            assert \forall integer f2, t2; 
                (f2 != f || t2 != t) ==> (count{Here}(g, f2, t2, 0, (i - 1)) ==  count{Pre}(g, f2, t2, 0, (i - 1)));
        */
        /*@ 
            assert \forall integer f2, t2; 
                (f2 != f || t2 != t) ==> (count{Here}(g, f2, t2, 0, i) ==  count{Pre}(g, f2, t2, 0, (i - 1)) + count{Pre}(g, f2, t2, (i - 1), i));
        */

        return;
    }

    /*@ loop invariant i >= 0;
        loop invariant i <= g->ecnt;
        loop invariant graph_valid(g);
        loop invariant \exists integer k; 
            (0 <= k < g->ecnt) && (g->edges[k].existent == 0);
        loop invariant \forall integer k; 
            (0 <= k < i) ==> (g->edges[k].existent != 0);
        loop invariant \forall integer f2, t2, m, n;
            count(g, f2, t2, m, n) == count{Pre}(g, f2, t2, m, n);

        loop variant g->ecnt - i;
    */
    for (int i = 0; i < g->ecnt; ++i) {
        Pre2:
        if (!g->edges[i].existent) {
            g->edges[i].from = f;
            g->edges[i].to = t;
	        g->edges[i].existent = 1;
            /*@ 
                ghost
                int j = 0;
                /@
                    loop invariant j >= 0;
                    loop invariant j <= g->esize;
                    loop invariant graph_valid(g);
                    loop invariant (j <= i) ==> count{Here}(g, f, t, 0, j) == count{Pre2}(g, f, t, 0, j);
                    loop invariant (j > i) ==> count{Here}(g, f, t, 0, j) == (count{Pre2}(g, f, t, 0, j) + 1);
                    loop invariant \forall integer k; 
                        (0 <= k <= j) && (k < g->esize) ==> 
                        (k != i) ==> 
                        (\at(g->edges[k].from, Pre2) == \at(g->edges[k].from, Here)) &&
                        (\at(g->edges[k].to, Pre2) == \at(g->edges[k].to, Here)) &&
                        (\at(g->edges[k].existent, Pre2) == \at(g->edges[k].existent, Here));
                    loop invariant \forall integer k;
                        (0 <= k < j) && (k != i)
                        ==>
                        (count{Pre2}(g, f, t, k, (k + 1)) == count{Here}(g, f, t, k, (k + 1)));
                    loop invariant (j < g->esize) ==> \valid(g->edges + (0..j));
                    loop invariant \forall integer f2, t2;
                        (j < i)
                        ==> 
                        (count{Pre2}(g, f2, t2, 0, (j + 1)) == count{Pre2}(g, f2, t2, 0, j) + count{Pre2}(g, f2, t2, j, (j + 1)));
                    loop invariant \forall integer f2, t2;
                        (i <= j < g->esize)
                        ==> 
                        (count{Pre2}(g, f2, t2, 0, (j + 1)) == count{Pre2}(g, f2, t2, 0, j) + count{Pre2}(g, f2, t2, j, (j + 1)));
                    loop invariant \forall integer f2, t2;
                        (i <= j < g->esize)
                        ==> 
                        (count{Here}(g, f2, t2, 0, (j + 1)) == count{Here}(g, f2, t2, 0, j) + count{Here}(g, f2, t2, j, (j + 1)));
                    loop invariant \forall integer k;
                        (0 <= k < g->esize) ==>
                            \forall integer f2, t2;
                                (f2 != f || t2 != t) ==>(count{Pre2}(g, f2, t2, 0, (k + 1)) == count{Pre2}(g, f2, t2, 0, k) + count{Pre2}(g, f2, t2, k, (k + 1)));
                    loop invariant \forall integer k;
                        (0 <= k < g->esize) ==>
                            \forall integer f2, t2;
                                (f2 != f || t2 != t) ==> (count{Here}(g, f2, t2, 0, (k + 1)) == count{Here}(g, f2, t2, 0, k) + count{Here}(g, f2, t2, k, (k + 1)));
                    loop invariant \forall integer k;
                        (0 <= k <= j - 1) ==>
                            \forall integer f2, t2;
                                (f2 != f || t2 != t) ==> (count{Here}(g, f2, t2, k, (k + 1)) == count{Pre2}(g, f2, t2, k, (k + 1)));
                    loop invariant \forall integer k; 
                        (0 <= k <= j)
                        ==>
                        \forall integer f2, t2;
                            (f2 != f || t2 != t) ==> count{Here}(g, f2, t2, 0, k) == count{Pre2}(g, f2, t2, 0, k);

                    loop variant g->esize - j;
                @/
                while (j < g->esize) {
                    j++;
                }
            */
            /*@ 
                assert \forall integer f2, t2; 
                (f2 != f || t2 != t) ==> (count{Here}(g, f2, t2, (j - 1), j) ==  count{Pre2}(g, f2, t2, (j - 1), j));
            */
            /*@ 
                assert \forall integer f2, t2; 
                    (f2 != f || t2 != t) ==> (count{Here}(g, f2, t2, 0, j) ==  count{Here}(g, f2, t2, 0, (j - 1)) + count{Here}(g, f2, t2, (j - 1), j));
            */
            /*@ 
                assert \forall integer f2, t2; 
                    (f2 != f || t2 != t) ==> (count{Pre2}(g, f2, t2, 0, j) ==  count{Pre2}(g, f2, t2, 0, (j - 1)) + count{Pre2}(g, f2, t2, (j - 1), j));
            */
            /*@ 
                assert \forall integer f2, t2; 
                    (f2 != f || t2 != t) ==> (count{Here}(g, f2, t2, 0, (j - 1)) ==  count{Pre2}(g, f2, t2, 0, (j - 1)));
            */
            /*@ 
                assert \forall integer f2, t2; 
                    (f2 != f || t2 != t) ==> (count{Here}(g, f2, t2, 0, j) ==  count{Pre2}(g, f2, t2, 0, (j - 1)) + count{Pre2}(g, f2, t2, (j - 1), j));
            */
	        return;
        }
    }
}


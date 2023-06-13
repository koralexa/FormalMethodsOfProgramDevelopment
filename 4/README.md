Программа тестировалась следующими способами:

# Тесты
Компиляция и запуск:

`> gcc -Wall main.c map.c -o map`

`> ./map`

Все тесты должны вернуть 0, результат запуска находится в файле tests/simple_tests.txt


# Санитайзеры address, undefined

Компиляция и запуск:

`> gcc -Wall -fsanitize=address,undefined main.c map.c -o map`

`> ./map`

Ошибки не обнаружены, результат запуска находится в файле tests/sanitize.txt

# Valgrind

Компиляция и запуск:

`> gcc -Wall -fsanitize=undefined main.c map.c -o map`

`> valgrind ./map`

Ошибки не обнаружены, результат запуска находится в файле tests/valgrind.txt

# Clang

Компиляция и запуск:

`> scan-build make map`

Ошибки не обнаружены, результат запуска находится в файле tests/clang.txt

# Тестовое покрытие (gcov, lcov)

Получение отчета:

`> gcc -Wall --coverage main.c map.c -o map`

`> ./map`

`> lcov -t "Map test coverage" -o map.info -c -d .`

`> genhtml -o test_coverage map.info`

Результат анализа находится в файле test_coverage/4/index.html
annotation redundant;
annotation nonredundant;

int: n;

array[1..n] of var 0..100: a;constraint (not ((sum(a) >= 0)));


solve satisfy;

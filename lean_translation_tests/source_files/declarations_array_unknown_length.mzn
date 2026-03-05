annotation redundant;
annotation nonredundant;

int: n;

array[1..n] of var 0..100: a;

constraint (sum(a) >= 0) :: redundant;

solve satisfy;

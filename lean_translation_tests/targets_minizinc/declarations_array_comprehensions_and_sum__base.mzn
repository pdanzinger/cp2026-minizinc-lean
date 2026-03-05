annotation redundant;
annotation nonredundant;

int: n;

array[1..n] of var int: arr = [i * 2 | i in 1..n];

constraint n >= 0;

solve satisfy;

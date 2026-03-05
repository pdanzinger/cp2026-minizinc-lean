annotation redundant;
annotation nonredundant;

int: n;

array[1..n] of var int: arr = [i * 2 | i in 1..n];

constraint n >= 0;
constraint (forall(i in 1..n)(arr[i] == 2*i)) :: redundant;

solve satisfy;

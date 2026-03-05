annotation redundant;
annotation nonredundant;

array[1..10] of var int: B;

constraint forall(i in 1..10)(B[i] == i);constraint (not ((min(i in 1..10)(B[i]) = 1)));


solve satisfy;

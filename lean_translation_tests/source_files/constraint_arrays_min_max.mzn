annotation redundant;
annotation nonredundant;

array[1..10] of var int: B;

constraint forall(i in 1..10)(B[i] == i);

constraint (min(i in 1..10)(B[i]) = 1) :: redundant;
constraint (max(i in 1..10)(B[i]) = 10) :: redundant;

solve satisfy;

annotation redundant;
annotation nonredundant;

array[1..10] of var int: A;
array[1..10] of var int: B;

constraint forall(i in 1..10)(A[i] >= i /\ A[i] <= i);
constraint forall(i in 1..10)(B[i] = A[i]);

constraint (sum(i in 1..10)(A[i]) == 55) :: redundant;
constraint (sum(i in 1..10)(B[i]) == 55) :: redundant;

constraint (sum(i in 1..10, j in i..i)(j) == 55) :: redundant;
constraint (sum(i in 1..10, j in i..i)(sum(j in 1..1)(j)) == 10) :: redundant;

solve satisfy;

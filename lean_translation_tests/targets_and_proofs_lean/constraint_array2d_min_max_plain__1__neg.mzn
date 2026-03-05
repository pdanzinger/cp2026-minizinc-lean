annotation redundant;
annotation nonredundant;

array[1..2, 1..2] of var int: A;

constraint forall(i in 1..2, j in 1..2)(A[i, j] = i + j);

constraint (max(A) = 3) :: nonredundant;

solve satisfy;

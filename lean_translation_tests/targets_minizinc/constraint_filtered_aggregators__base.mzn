annotation redundant;
annotation nonredundant;

array[1..2] of var 1..2: A;
array[1..2] of var bool: B;

constraint A[1] = 1 /\ A[2] = 2;
constraint B[1] = true /\ B[2] = false;

solve satisfy;

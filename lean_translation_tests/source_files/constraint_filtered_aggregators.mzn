annotation redundant;
annotation nonredundant;

array[1..2] of var 1..2: A;
array[1..2] of var bool: B;

constraint A[1] = 1 /\ A[2] = 2;
constraint B[1] = true /\ B[2] = false;

constraint (exists(i in 1..2 where A[i] >= 1)(10 div A[i] = 10 div A[i])) :: redundant;
constraint (sum(i in 1..2 where A[i] >= 1)(10 div A[i]) = 15) :: redundant;
constraint (min(i in 1..2)(10 div A[i]) = 5) :: redundant;
constraint (max(i in 1..2)(10 div A[i]) = 10) :: redundant;
constraint (exists(i in 1..2 where B[i])(A[i] = i)) :: redundant;

constraint (sum(i in 1..2 where A[i] >= 1)(10 div A[i]) = 14) :: nonredundant;

solve satisfy;

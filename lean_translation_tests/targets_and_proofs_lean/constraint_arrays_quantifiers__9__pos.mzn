annotation redundant;
annotation nonredundant;

int: x = 100;

array[1..10] of var int: A;
array[1..10] of var int: B;

constraint forall(i in 1..10)(A[i] >= i /\ A[i] <= i);
constraint forall(i in 1..10)(B[i] = A[i]);
constraint (exists(y in 1..1, x in y..y)(x = 1)) :: redundant;


solve satisfy;

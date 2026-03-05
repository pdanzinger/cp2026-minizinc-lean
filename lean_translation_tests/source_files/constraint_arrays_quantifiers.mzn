annotation redundant;
annotation nonredundant;

int: x = 100;

array[1..10] of var int: A;
array[1..10] of var int: B;

constraint forall(i in 1..10)(A[i] >= i /\ A[i] <= i);
constraint forall(i in 1..10)(B[i] = A[i]);

constraint (forall(i in 1..10)(A[i] = i)) :: redundant;
constraint (forall(i in 1..10)(B[i] = i)) :: redundant;

constraint (exists(i in 1..10)(A[i] = 5)) :: redundant;
constraint (exists(i in 1..10)(B[i] = 5)) :: redundant;

constraint (forall(x in 1..10)(x < 100)) :: redundant;
constraint (exists(x in 1..10)(x < 100)) :: redundant;

constraint (forall(x in 1..10)(forall(x in 100..100)(x = 100))) :: redundant;
constraint (exists(x in 1..10)(forall(x in 100..100)(x = 100))) :: redundant;

constraint (forall(y in 1..1, x in y..y)(x = 1)) :: redundant;
constraint (exists(y in 1..1, x in y..y)(x = 1)) :: redundant;


solve satisfy;

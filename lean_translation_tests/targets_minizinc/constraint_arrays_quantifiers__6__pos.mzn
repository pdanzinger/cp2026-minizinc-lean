annotation redundant;
annotation nonredundant;

int: x = 100;

array[1..10] of var int: A;
array[1..10] of var int: B;

constraint forall(i in 1..10)(A[i] >= i /\ A[i] <= i);
constraint forall(i in 1..10)(B[i] = A[i]);constraint (not ((forall(x in 1..10)(forall(x in 100..100)(x = 100)))));



solve satisfy;

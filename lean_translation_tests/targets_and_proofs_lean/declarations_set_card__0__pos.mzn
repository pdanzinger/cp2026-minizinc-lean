annotation redundant;
annotation nonredundant;

set of int: S;

array[S] of var int: A;

constraint card(S) >= 1;
constraint forall(i in S)(A[i] >= i /\ A[i] <= i);

constraint (exists(i in S)(A[i] = i)) :: redundant;

solve satisfy;

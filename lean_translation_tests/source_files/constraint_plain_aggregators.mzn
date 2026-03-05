annotation redundant;
annotation nonredundant;

set of int: S = {2, 4, 5};
array[1..3] of var int: A = [2, 4, 5];
array[1..2] of var bool: B;

constraint B[1] = true /\ B[2] = false;

constraint ((min(S) = 2) /\ (max(S) = 5)) :: redundant;
constraint ((min(A) = 2) /\ (max(A) = 5)) :: redundant;
constraint ((exists(B)) /\ (not (forall(B)))) :: redundant;

constraint (max(A) = 4) :: nonredundant;

solve satisfy;

annotation redundant;
annotation nonredundant;

set of int: S = {2, 4, 5};
array[1..3] of var int: A = [2, 4, 5];
array[1..2] of var bool: B;

constraint B[1] = true /\ B[2] = false;constraint (not (((exists(B)) /\ (not (forall(B))))));


solve satisfy;

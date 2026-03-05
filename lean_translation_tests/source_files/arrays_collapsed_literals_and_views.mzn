annotation redundant;
annotation nonredundant;

array[1..4] of var int: C = [i + j | i in 1..2, j in 1..2];
array[1..11] of var int: L = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
array[1..8] of var int: B0 = [1, 2, 3, 4, 5, 6, 7, 8];
array[1..2, 1..2, 1..2] of var int: A3 = array3d(1..2, 1..2, 1..2, B0);
array[1..1] of var int: S0 = [42];
array[1..1, 1..1, 1..1, 1..1, 1..1, 1..1] of var int: A6 =
    array6d(1..1, 1..1, 1..1, 1..1, 1..1, 1..1, S0);

constraint (
    (C[1] = 2) /\
    (C[2] = 3) /\
    (C[3] = 3) /\
    (C[4] = 4) /\
    (sum(C) = 12)
) :: redundant;

constraint (L = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) :: redundant;
constraint (L != [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12]) :: redundant;
constraint ((A3[1, 1, 1] = 1) /\ (A3[2, 2, 2] = 8)) :: redundant;
constraint (A6[1, 1, 1, 1, 1, 1] = 42) :: redundant;

constraint (sum(C) = 11) :: nonredundant;

solve satisfy;

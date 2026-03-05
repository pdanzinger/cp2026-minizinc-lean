annotation redundant;
annotation nonredundant;

array[1..4] of var int: C = [i + j | i in 1..2, j in 1..2];
array[1..11] of var int: L = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
array[1..8] of var int: B0 = [1, 2, 3, 4, 5, 6, 7, 8];
array[1..2, 1..2, 1..2] of var int: A3 = array3d(1..2, 1..2, 1..2, B0);
array[1..1] of var int: S0 = [42];
array[1..1, 1..1, 1..1, 1..1, 1..1, 1..1] of var int: A6 =
    array6d(1..1, 1..1, 1..1, 1..1, 1..1, 1..1, S0);

constraint (sum(C) = 11) :: nonredundant;

solve satisfy;

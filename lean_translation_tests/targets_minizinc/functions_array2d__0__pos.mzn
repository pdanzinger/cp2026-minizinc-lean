annotation redundant;
annotation nonredundant;

array[1..2, 1..2] of var int: A = array2d(1..2, 1..2, [1,2,3,4]);constraint (not ((A[1,1] == 1 /\ A[1,2] == 2 /\ A[2,1] == 3 /\ A[2,2] == 4)));


solve satisfy;

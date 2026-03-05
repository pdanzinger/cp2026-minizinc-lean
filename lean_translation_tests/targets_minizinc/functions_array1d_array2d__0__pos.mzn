annotation redundant;
annotation nonredundant;

array[11..14] of var int: A0 = array1d(11..14, [1,2,3,4]);

array[1..2, 1..2] of var int: A = array2d(1..2, 1..2, A0);constraint (not ((A[1,1] == 1 /\ A[1,2] == 2 /\ A[2,1] == 3 /\ A[2,2] == 4)));


solve satisfy;

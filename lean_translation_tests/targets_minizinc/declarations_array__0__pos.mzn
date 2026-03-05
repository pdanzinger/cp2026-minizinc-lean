annotation redundant;
annotation nonredundant;

array[1..2] of var int: A;

constraint A[1] = 10 /\ A[2] = 5;constraint (not ((A[1] = 10)));


solve satisfy;

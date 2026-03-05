annotation redundant;
annotation nonredundant;

array[1..2] of var set of 1..3: A = [{1}, {1, 2}];constraint (not ((3 in A[1])));


solve satisfy;

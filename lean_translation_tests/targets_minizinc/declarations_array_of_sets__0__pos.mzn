annotation redundant;
annotation nonredundant;

array[1..2] of var set of 1..3: A = [{1}, {1, 2}];constraint (not ((
    (card(A[1]) = 1) /\
    (card(A[2]) = 2) /\
    (1 in A[1]) /\
    (2 in A[2]) /\
    (A[1] union A[2] = {1, 2})
)));


solve satisfy;

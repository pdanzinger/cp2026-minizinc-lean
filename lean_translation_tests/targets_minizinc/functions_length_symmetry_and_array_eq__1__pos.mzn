annotation redundant;
annotation nonredundant;

array[2..4] of var int: A = array1d(2..4, [5, 6, 7]);
array[1..2, 1..2] of var int: B = array2d(1..2, 1..2, [1, 2, 3, 4]);constraint (not ((length(B) = 4)));


solve satisfy;

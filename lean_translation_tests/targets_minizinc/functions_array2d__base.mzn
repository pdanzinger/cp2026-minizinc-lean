annotation redundant;
annotation nonredundant;

array[1..2, 1..2] of var int: A = array2d(1..2, 1..2, [1,2,3,4]);

solve satisfy;

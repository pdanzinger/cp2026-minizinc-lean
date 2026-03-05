annotation redundant;
annotation nonredundant;

include "all_different.mzn";

array[1..3] of var int: x = [1, 2, 3];
constraint (alldifferent(x)) :: redundant;

solve satisfy;

annotation redundant;
annotation nonredundant;

include "all_different.mzn";

array[1..3] of var int: x = [1, 2, 3];constraint (not ((all_different([1, 1, 2]))));


solve satisfy;

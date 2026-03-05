annotation redundant;
annotation nonredundant;

set of int: S = {1, 3, 4};
set of int: T = {3, 4};constraint (not ((3 in (S diff T))));


solve satisfy;

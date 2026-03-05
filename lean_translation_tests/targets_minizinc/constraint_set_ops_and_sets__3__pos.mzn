annotation redundant;
annotation nonredundant;

set of int: S = {1, 3, 4};
set of int: T = {3, 4};constraint (not (({i + 1 | i in S where i < 4} = {2, 4})));


solve satisfy;

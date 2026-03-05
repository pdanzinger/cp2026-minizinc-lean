annotation redundant;
annotation nonredundant;

set of int: S = {1, 3, 4};
set of int: T = {3, 4};

constraint (card(S union {2}) = 4) :: redundant;

solve satisfy;

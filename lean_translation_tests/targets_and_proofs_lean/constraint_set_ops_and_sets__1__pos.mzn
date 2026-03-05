annotation redundant;
annotation nonredundant;

set of int: S = {1, 3, 4};
set of int: T = {3, 4};

constraint (
    ((S diff T) = {1}) /\
    (1 in (S diff T))
) :: redundant;

solve satisfy;

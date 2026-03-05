annotation redundant;
annotation nonredundant;

set of int: S = {1, 3, 4};
set of int: T = {3, 4};

constraint (
    ((S intersect T) = {3, 4}) /\
    (S != T)
) :: redundant;

solve satisfy;

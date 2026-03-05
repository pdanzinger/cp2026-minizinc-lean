annotation redundant;
annotation nonredundant;

set of int: S = {1, 3, 4};
set of int: T = {3, 4};

constraint (card(S union {2}) = 4) :: redundant;

constraint (
    ((S diff T) = {1}) /\
    (1 in (S diff T))
) :: redundant;

constraint (
    ((S intersect T) = {3, 4}) /\
    (S != T)
) :: redundant;

constraint ({i + 1 | i in S where i < 4} = {2, 4}) :: redundant;

constraint (3 in (S diff T)) :: nonredundant;

solve satisfy;

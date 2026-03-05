annotation redundant;
annotation nonredundant;

set of bool: SB = {false, true};

constraint (card(SB) = 2) :: redundant;

constraint (card(SB) = 1) :: nonredundant;

solve satisfy;

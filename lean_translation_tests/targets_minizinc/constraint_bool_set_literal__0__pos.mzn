annotation redundant;
annotation nonredundant;

set of bool: SB = {false, true};constraint (not ((card(SB) = 2)));


solve satisfy;

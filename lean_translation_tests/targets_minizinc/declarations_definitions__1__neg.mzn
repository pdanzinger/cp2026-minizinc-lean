annotation redundant;
annotation nonredundant;

var int: a = 10;constraint (not ((a = 9)));


solve satisfy;

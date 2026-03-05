annotation redundant;
annotation nonredundant;

var int: a = 10;

constraint (a = 9) :: nonredundant;

solve satisfy;

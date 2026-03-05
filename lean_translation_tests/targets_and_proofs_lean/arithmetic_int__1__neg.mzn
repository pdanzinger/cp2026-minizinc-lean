annotation redundant;
annotation nonredundant;

var int: a;
var int: b;
var int: c;

constraint a = 10;
constraint b = 5;

constraint (c = 10) :: nonredundant;

solve satisfy;

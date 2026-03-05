annotation redundant;
annotation nonredundant;

var int: a;
var int: b;
var int: c;

constraint a = 10;
constraint b = 5;

solve satisfy;

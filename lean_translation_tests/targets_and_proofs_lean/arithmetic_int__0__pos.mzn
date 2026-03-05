annotation redundant;
annotation nonredundant;

var int: a;
var int: b;
var int: c;

constraint a = 10;
constraint b = 5;

constraint (a + b = 15 /\ a - b = 5 /\ a * b = 50) :: redundant;

solve satisfy;

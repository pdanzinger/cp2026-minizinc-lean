annotation redundant;
annotation nonredundant;

var bool: a;
var bool: b;

constraint (a = true);
constraint (b = false);
constraint (a <-> a) :: redundant;

solve satisfy;

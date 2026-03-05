annotation redundant;
annotation nonredundant;

var bool: a;
var bool: b;

constraint (a = true);
constraint (b = false);
constraint (a xor b) :: redundant;

solve satisfy;

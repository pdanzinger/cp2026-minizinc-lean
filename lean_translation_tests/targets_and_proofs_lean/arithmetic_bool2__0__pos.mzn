annotation redundant;
annotation nonredundant;

var bool: a;
var bool: b;

constraint (a = true);
constraint (b = false);

constraint (not (b xor b)) :: redundant;

solve satisfy;

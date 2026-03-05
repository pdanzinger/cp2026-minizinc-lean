annotation redundant;
annotation nonredundant;

var bool: a;
var bool: b;

constraint (a = true);
constraint (b = false);

constraint (not (b xor b)) :: redundant;
constraint (not (a <-> b)) :: redundant;
constraint (a <-> a) :: redundant;
constraint (b <-> b) :: redundant;

solve satisfy;

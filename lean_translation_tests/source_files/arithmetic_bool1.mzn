annotation redundant;
annotation nonredundant;

var bool: a;
var bool: b;

constraint (a = true);
constraint (b = false);

constraint (not (not true)) :: redundant;
constraint (not false) :: redundant;

constraint (a \/ b) :: redundant;
constraint (not (a /\ b)) :: redundant;
constraint (a xor b) :: redundant;
constraint (not (a xor a)) :: redundant;

solve satisfy;

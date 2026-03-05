annotation redundant;
annotation nonredundant;

var bool: a;
var bool: b;

constraint (a = true);
constraint (b = false);constraint (not ((b <-> b)));


solve satisfy;

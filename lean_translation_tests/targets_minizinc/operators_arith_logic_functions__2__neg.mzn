annotation redundant;
annotation nonredundant;

var int: a;
var bool: p;
var bool: q;

constraint a = 2;
constraint p = true;
constraint q = false;constraint (not ((max(a, 5) = 2)));


solve satisfy;

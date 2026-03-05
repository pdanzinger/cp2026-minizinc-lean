annotation redundant;
annotation nonredundant;

var int: a;
var bool: p;
var bool: q;

constraint a = 2;
constraint p = true;
constraint q = false;

constraint (
    (p -> p) /\
    (not (p -> q)) /\
    (p <- q)
) :: redundant;

solve satisfy;

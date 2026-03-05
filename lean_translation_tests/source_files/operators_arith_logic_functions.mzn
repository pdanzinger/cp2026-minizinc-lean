annotation redundant;
annotation nonredundant;

var int: a;
var bool: p;
var bool: q;

constraint a = 2;
constraint p = true;
constraint q = false;

constraint (
    ((+2) = 2) /\
    ((-a) = -2) /\
    (min(a, 5) = 2) /\
    (max(a, 5) = 5) /\
    (a ^ 2 = 4) /\
    (a ^ (-1) = 0)
) :: redundant;

constraint (
    (p -> p) /\
    (not (p -> q)) /\
    (p <- q)
) :: redundant;

constraint (max(a, 5) = 2) :: nonredundant;

solve satisfy;

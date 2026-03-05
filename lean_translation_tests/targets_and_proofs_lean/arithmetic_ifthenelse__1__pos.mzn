annotation redundant;
annotation nonredundant;

var int: a;
var int: b;
var int: c;

constraint a = 10;
constraint (if a!=10 then false else true endif) :: redundant;


solve satisfy;

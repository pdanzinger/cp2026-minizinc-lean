annotation redundant;
annotation nonredundant;

var int: a;
var int: b;
var int: c;

constraint a = 10;

constraint (if a=10 then true else false endif) :: redundant;


solve satisfy;

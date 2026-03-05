annotation redundant;
annotation nonredundant;

var bool: x;
var bool: y;

constraint x == true /\ y == false;

constraint (bool2int(x) != 1 \/ bool2int(y) != 0) :: nonredundant;


solve satisfy;

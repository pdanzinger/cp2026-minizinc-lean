annotation redundant;
annotation nonredundant;

var bool: x;
var bool: y;

constraint x == true /\ y == false;


solve satisfy;

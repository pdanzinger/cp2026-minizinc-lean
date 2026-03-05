annotation redundant;
annotation nonredundant;

var bool: x;
var bool: y;

constraint x == true /\ y == false;constraint (not ((bool2int(x) == 1 /\ bool2int(y) == 0)));



solve satisfy;

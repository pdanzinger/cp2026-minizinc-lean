annotation redundant;
annotation nonredundant;

var 0..10: a;
var 0..10: b;
constraint (a <= 9) :: nonredundant;

solve satisfy;

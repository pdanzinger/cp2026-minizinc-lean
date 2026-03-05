annotation redundant;
annotation nonredundant;

var 0..10: a;
var 0..10: b;

constraint (1 <= a) :: nonredundant;

solve satisfy;

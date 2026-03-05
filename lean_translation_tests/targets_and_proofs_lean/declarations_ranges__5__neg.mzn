annotation redundant;
annotation nonredundant;

var 0..10: a;
var 0..10: b;
constraint (a + b <= 19) :: nonredundant;

solve satisfy;

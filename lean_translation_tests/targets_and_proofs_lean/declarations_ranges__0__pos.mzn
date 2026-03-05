annotation redundant;
annotation nonredundant;

var 0..10: a;
var 0..10: b;

constraint (0 <= a /\ a <= 10) :: redundant;

solve satisfy;

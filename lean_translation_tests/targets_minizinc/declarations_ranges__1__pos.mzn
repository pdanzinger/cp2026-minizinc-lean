annotation redundant;
annotation nonredundant;

var 0..10: a;
var 0..10: b;constraint (not ((0 <= a + b /\ a + b <= 20)));


solve satisfy;

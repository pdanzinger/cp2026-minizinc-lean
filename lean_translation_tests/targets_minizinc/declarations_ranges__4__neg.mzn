annotation redundant;
annotation nonredundant;

var 0..10: a;
var 0..10: b;constraint (not ((1 <= a + b)));


solve satisfy;

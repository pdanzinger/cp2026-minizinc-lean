annotation redundant;
annotation nonredundant;

var 0..10: a;
var 0..10: b;constraint (not ((a + b <= 19)));


solve satisfy;

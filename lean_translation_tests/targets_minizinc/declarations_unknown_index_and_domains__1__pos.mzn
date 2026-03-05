annotation redundant;
annotation nonredundant;

var 0..10: a = 5;
var set of 1..4: X = {1, 4};
array[int] of var 0..1: U;constraint (not (((card(X) = 2) /\ (1 in X) /\ (4 in X))));


solve satisfy;

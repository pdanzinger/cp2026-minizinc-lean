annotation redundant;
annotation nonredundant;

var 0..10: a = 5;
var set of 1..4: X = {1, 4};
array[int] of var 0..1: U;
constraint (((1 in X) -> (1 in 1..4)) /\ ((4 in X) -> (4 in 1..4))) :: redundant;

solve satisfy;

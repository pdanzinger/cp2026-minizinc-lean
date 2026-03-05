annotation redundant;
annotation nonredundant;

var 0..10: a = 5;
var set of 1..4: X = {1, 4};
array[int] of var 0..1: U;

constraint (card(X) = 3) :: nonredundant;

solve satisfy;

annotation redundant;
annotation nonredundant;

var 0..10: a;
var 0..10: b;

constraint (0 <= a /\ a <= 10) :: redundant;
constraint (0 <= a + b /\ a + b <= 20) :: redundant;

constraint (1 <= a) :: nonredundant;
constraint (a <= 9) :: nonredundant;
constraint (1 <= a + b) :: nonredundant;
constraint (a + b <= 19) :: nonredundant;

solve satisfy;

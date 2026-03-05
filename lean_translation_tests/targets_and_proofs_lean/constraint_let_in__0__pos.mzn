annotation redundant;
annotation nonredundant;

var int: x;

constraint (x*x*x == let {var int: sq = x*x; } in sq*x) :: redundant;

solve satisfy;

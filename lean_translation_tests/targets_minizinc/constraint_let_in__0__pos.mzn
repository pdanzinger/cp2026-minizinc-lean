annotation redundant;
annotation nonredundant;

var int: x;constraint (not ((x*x*x == let {var int: sq = x*x; } in sq*x)));


solve satisfy;

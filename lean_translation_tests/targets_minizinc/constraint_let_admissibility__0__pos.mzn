annotation redundant;
annotation nonredundant;constraint (not ((let {var 0..2: y = 2;} in y = 2)));


solve satisfy;

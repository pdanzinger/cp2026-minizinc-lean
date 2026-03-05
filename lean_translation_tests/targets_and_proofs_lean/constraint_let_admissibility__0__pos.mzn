annotation redundant;
annotation nonredundant;

constraint (let {var 0..2: y = 2;} in y = 2) :: redundant;

solve satisfy;

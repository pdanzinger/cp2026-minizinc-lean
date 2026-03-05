annotation redundant;
annotation nonredundant;

constraint (let {var 0..2: y = 2;} in y = 1) :: nonredundant;

solve satisfy;

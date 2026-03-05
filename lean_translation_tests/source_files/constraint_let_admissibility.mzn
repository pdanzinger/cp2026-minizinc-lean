annotation redundant;
annotation nonredundant;

constraint (let {var 0..2: y = 2;} in y = 2) :: redundant;

constraint (
    let {array[1..2] of var 0..2: y = [1, 2];}
    in (y[1] = 1 /\ y[2] = 2 /\ sum(y) = 3)
) :: redundant;

constraint (let {var 0..2: y = 2;} in y = 1) :: nonredundant;

solve satisfy;

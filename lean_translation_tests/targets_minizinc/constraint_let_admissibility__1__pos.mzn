annotation redundant;
annotation nonredundant;constraint (not ((
    let {array[1..2] of var 0..2: y = [1, 2];}
    in (y[1] = 1 /\ y[2] = 2 /\ sum(y) = 3)
)));


solve satisfy;

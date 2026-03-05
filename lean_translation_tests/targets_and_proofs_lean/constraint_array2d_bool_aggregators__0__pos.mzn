annotation redundant;
annotation nonredundant;

array[1..2, 1..2] of var bool: B;

constraint (
    B[1, 1] = true /\
    B[1, 2] = true /\
    B[2, 1] = true /\
    B[2, 2] = false
);

constraint ((exists(i, j in 1..2)(B[i,j])) /\ (not (forall(i, j in 1..2)(B[i,j])))) :: redundant;

solve satisfy;

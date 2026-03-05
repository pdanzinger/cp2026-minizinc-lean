annotation redundant;
annotation nonredundant;


constraint (
    1 >= 0 /\
    1 > 0  /\
    1 >= 1 /\
    0 <= 1 /\
    0 < 1  /\
    0 <= 0 /\
    1 == 1 /\
    1 != 0
) :: redundant;


solve satisfy;

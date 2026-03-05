annotation redundant;
annotation nonredundant;

constraint (not(
    0 >= 1 \/
    0 > 1  \/
    1 <= 0 \/
    1 < 0  \/
    1 != 1 \/
    1 == 0
)) :: redundant;


solve satisfy;

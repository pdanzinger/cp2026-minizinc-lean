annotation redundant;
annotation nonredundant;constraint (not ((not(
    0 >= 1 \/
    0 > 1  \/
    1 <= 0 \/
    1 < 0  \/
    1 != 1 \/
    1 == 0
))));



solve satisfy;

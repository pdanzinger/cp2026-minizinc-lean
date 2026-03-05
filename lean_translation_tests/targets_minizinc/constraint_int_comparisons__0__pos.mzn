annotation redundant;
annotation nonredundant;constraint (not ((
    1 >= 0 /\
    1 > 0  /\
    1 >= 1 /\
    0 <= 1 /\
    0 < 1  /\
    0 <= 0 /\
    1 == 1 /\
    1 != 0
)));



solve satisfy;

annotation redundant;
annotation nonredundant;

constraint (
    let {
        var int: y = 1;
        var int: z = y + 1;
    } in z = 2
) :: redundant;

solve satisfy;

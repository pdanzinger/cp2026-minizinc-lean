annotation redundant;
annotation nonredundant;constraint (not ((
    let {
        var int: y = 1;
        var int: z = y + 1;
    } in z = 2
)));


solve satisfy;

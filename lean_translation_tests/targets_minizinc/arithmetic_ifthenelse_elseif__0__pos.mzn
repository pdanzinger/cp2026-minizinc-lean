annotation redundant;
annotation nonredundant;

var int: a;

constraint a = 2;constraint (not ((if a = 1 then false elseif a = 2 then true else false endif)));


solve satisfy;

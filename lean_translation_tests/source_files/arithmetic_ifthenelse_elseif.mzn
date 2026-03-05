annotation redundant;
annotation nonredundant;

var int: a;

constraint a = 2;

constraint (if a = 1 then false elseif a = 2 then true else false endif) :: redundant;

constraint (if a = 1 then true elseif a = 2 then false else true endif) :: nonredundant;

solve satisfy;

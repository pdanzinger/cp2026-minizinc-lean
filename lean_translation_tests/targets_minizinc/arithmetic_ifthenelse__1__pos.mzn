annotation redundant;
annotation nonredundant;

var int: a;
var int: b;
var int: c;

constraint a = 10;constraint (not ((if a!=10 then false else true endif)));



solve satisfy;

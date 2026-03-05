annotation redundant;
annotation nonredundant;

include "circuit.mzn";
include "alldifferent.mzn";


array[1..3] of var 1..3: x;
constraint circuit(x) /\ alldifferent(x);

solve satisfy;

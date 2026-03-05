annotation redundant;
annotation nonredundant;

include "circuit.mzn";
include "alldifferent.mzn";


array[1..3] of var 1..3: x;
constraint circuit(x) /\ alldifferent(x);constraint (not ((
  not (x[1]=1 /\ x[2]=2 /\ x[3]=3) /\
  not (x[1]=1 /\ x[2]=3 /\ x[3]=2) /\
  not (x[1]=2 /\ x[2]=1 /\ x[3]=3) /\
  not (x[1]=3 /\ x[2]=2 /\ x[3]=1)
)));


solve satisfy;

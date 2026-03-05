annotation redundant;
annotation nonredundant;

include "cumulative.mzn";

int: N;
int: M;
constraint M>=0;
var int: b;
constraint b >= 0;

array[1..N] of var 0..M: starts;
array[1..N] of var 0..M: durations;
array[1..N] of var 0..M: reqs;
array[1..N] of var 0..0: reqs_zero;

constraint cumulative(starts, durations, reqs, b);

var bool: c1 = cumulative(starts, durations, reqs, b*2);
constraint (c1) :: redundant;
var bool: c2 = cumulative(starts, durations, reqs_zero, 0);
constraint (c2) :: redundant;
var bool: c3 = not (N >= 1 /\ reqs[1] > b /\ durations[1] >= 1);
constraint (c3) :: redundant;

var bool: c4 = cumulative(starts, durations, reqs, b-1);
constraint (c4) :: nonredundant;

solve satisfy;

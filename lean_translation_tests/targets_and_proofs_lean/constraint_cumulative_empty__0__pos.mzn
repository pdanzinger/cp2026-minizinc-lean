annotation redundant;
annotation nonredundant;

include "cumulative.mzn";

int: N = 0;

array[1..N] of var 0..0: starts;
array[1..N] of var 0..0: durations;
array[1..N] of var 0..0: reqs;

constraint cumulative(starts, durations, reqs, 0);

var bool: c = cumulative(starts, durations, reqs, 0);

constraint (c) :: redundant;

solve satisfy;

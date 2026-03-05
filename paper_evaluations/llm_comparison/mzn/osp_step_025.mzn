annotation redundant;

solve :: seq_search([
  int_search([b], input_order, indomain_min, complete),
  int_search(
  [
    [batch_for_job[j],
    machine_for_job[j],
    start_times[machine_for_job[j],batch_for_job[j]],
    duration[machine_for_job[j],batch_for_job[j]]
  ][i] | j in 1..n, i in 1..4],
  first_fail, indomain_min, complete)
  ]) minimize objective;


var 1..n: b;  %total number of batches that are used

%total number of batches used
constraint
  b = sum(ma in MACHINES, ba in 1..n)(1-empty_batch[ma,ba])
;

include "globals.mzn";

%%---------Input------------------------------------------------------------------------------------------------------------------------------------------

int: l; %scheduling horizon
set of int: TIMES = 0..l;
int: a; %number of attributes
set of int: ATTRIBUTES = 0..a;
% do we need set of attributes?
array[1..a+1,1..a] of int: setup_costs; %setup_costs[i,j] costs for switching from attribute i to attribute j
%setup_costs including attribute 0 for empty batches
array[0..a+1,0..a] of int: setup_costs_mod
= array2d(0..a+1,0..a, [(if (i >= 1 /\ j >= 1) then setup_costs[i,j] else 0 endif)| i in 0..a+1, j in 0..a]);
array[1..a+1,1..a] of int: setup_times; %setup_times[i,j] time for switching from attribute i to attribute j
%setup_times including attribute 0 for empty batches
array[0..a+1,0..a] of int: setup_times_mod
= array2d(0..a+1,0..a, [(if (i >= 1 /\ j >= 1) then setup_times[i,j] else 0 endif)| i in 0..a+1, j in 0..a]);
int: m; %number of machines
set of int: MACHINES = 1..m;
array[1..m] of int: min_cap; %minimum capacity per machine
array[1..m] of int: max_cap; %maximum capacity per machine
array[MACHINES] of int: initState; %initial state (=attribute) of every machine
int: s; %maximum number of shifts per machine
array[MACHINES,1..s] of TIMES: m_a_s; %machine availability start times
array[MACHINES,1..s] of TIMES: m_a_e; %machine availability end times
%machine availability start times and end times including an extra shift of length 0 at end (for empty batches)
array[MACHINES,1..s+1] of TIMES: m_a_s_mod
= array2d(MACHINES,1..s+1, [(if (j <= s) then m_a_s[ma,j] else l endif)| ma in MACHINES, j in 1..s+1]);
array[MACHINES,1..s+1] of TIMES: m_a_e_mod
= array2d(MACHINES,1..s+1, [(if (j <= s) then m_a_e[ma,j] else l endif)| ma in MACHINES, j in 1..s+1]);
int: n; %number of jobs
array[1..n] of set of 1..m: eligible_machine; %eligible_machine[i] contains j <-> job i can be executed on machine j
array[1..n] of int: earliest_start; %earliest start date for every job
array[1..n] of int: latest_end; %latest end date for every job
array[1..n] of int: min_time; %minimum time in machine for every job
array[1..n] of int: max_time; %maximum time in machine for every job
array[1..n] of int: size; %occupied space in machine for every job
array[1..n] of int: attribute; %attribute of every job

%new
%constants needed for the calculation of the objective function
int: upper_bound_integer_objective;
int: mult_factor_total_runtime;
int: mult_factor_finished_toolate;
int: mult_factor_total_setuptimes;
int: mult_factor_total_setupcosts;
int: running_time_bound;
int: min_duration;
int: max_duration;
int: max_setup_time;
int: max_setup_cost;
%end new

%%---------Decision variables-----------------------------------------------------------------------------------------------------------------------------

array[MACHINES,1..n] of var TIMES: start_times; %start_times[ma,ba] is start time of batch ba on machine ma
array[MACHINES,1..n] of var 0..max_duration: duration; %duration[ma,ba] is duration of batch ba on machine ma
array[MACHINES,1..n,1..n] of var 0..1: job_in_batch; %job_in_batch[ma,ba,j]=1 if job j is in batch ba on machine ma

%helper variables
array[MACHINES,1..n] of var 0..1: empty_batch; %empty_batch[ma,ba]=1 if the batch ba on machine ma is empty
%var 1..n: b;  %total number of batches that are used
array[MACHINES,1..n] of var ATTRIBUTES: attribute_for_batch; %attribute_for_batch[ma,ba] is attribute of all jobs in batch ba on machine ma
array[MACHINES, 1..n-1] of var 0..max_setup_time:setup_times_between_batches; %array of setup times between batches
array[MACHINES, 1..n-1] of var 0..max_setup_cost:setup_costs_between_batches; %array of setup times between batches
array[MACHINES,1..n,1..s+1] of var 0..1: batch_in_shift; %batch_in_shift[ma,ba,j]=1 if batch ba on machine ma is in shift j, 0 otherwise
array[1..n,MACHINES,1..n] of var 0..1: late_job; %late_job[j,ma,ba]=1 if job is in batch ba on machine ba and is late
%array[1..n] of var 0..1: late_job2; %late_job[j]=1 if job is late

%%---------Constraints------------------------------------------------------------------------------------------------------------------------------------

% General note on how constraints are formulated:
% for binary variables: "if a then b" translates to "b>=a"
% ("if a then b" translates to "!a or b" which is equivalent to "(1-a)+b>=1" or "b>=a")
% for a,x,y  binary variables: "if a=1 then x=y" translates to "1 >= a +x-y /\ 1 >= a -x+y"
% (if a=1 we have 0 >=x-y /\ 0 >= -x+y and thus x=y)

%every job is scheduled to exactly one batch
constraint forall (j in 1..n) (
  sum (ma in MACHINES, ba in 1..n)(job_in_batch[ma,ba,j]) = 1
);

%job must be scheduled to a machine that is eligible
constraint forall (j in 1..n)(
  sum (ma in eligible_machine[j], ba in 1..n)(job_in_batch[ma,ba,j]) = 1
);



% attribute of batch must be equal to attribute of all jobs in batch
% if job_in_batch[ma,b,j]=1  attribue_for_batch[ma,ba]=attribute[j]
% explanation of the inequalities below:
% if job_in_batch[ma,b,j]=1 the 1st inequality becomes: attribute_for_batch[ma,ba]<=attribute[j]
% the 2nd inequality is: attribute_for_batch[ma,ba]>=attribute[j]
% otherwise: attribute_for_batch[ma,ba]<=a /\ attribute_for_batch[ma,ba] >= 0
constraint forall (ma in MACHINES, ba in 1..n, j in 1..n)(
  attribute_for_batch[ma,ba] <= attribute[j]*job_in_batch[ma,ba,j] + a*(1-job_in_batch[ma,ba,j])
  /\
  attribute_for_batch[ma,ba] >= attribute[j]*job_in_batch[ma,ba,j]
);

% empty batches are scheduled at the end of the interval:
% 0.a) if no job is scheduled to ba on ma, empty_batch[ma,ba] is set to 1
% b) and vice versa
% 1.if batch ba on machine ma is empty, all following batches on same machine are also empty
% 2. start times are set to l
% 3. duration is set to 0
% 4. attribute is set to 0
% 5. shift is set to last shift on machine (in modified list of shifts)
% 0.a)
constraint forall (ma in MACHINES, ba in 1..n) (
   sum(j in 1..n) (job_in_batch[ma,ba,j]) >= 1-empty_batch[ma,ba]
);
% 0.b)
constraint forall (ma in MACHINES, ba in 1..n, j in 1..n) (
   job_in_batch[ma,ba,j] <= 1-empty_batch[ma,ba]
);
%1
constraint forall (ma in MACHINES, ba in 1..n-1)(
  empty_batch[ma,ba] <= empty_batch[ma,ba+1]
);
%2
constraint forall (ma in MACHINES, ba in 1..n)(
  l*empty_batch[ma,ba] <= start_times[ma,ba]
);
%3
constraint forall (ma in MACHINES, ba in 1..n)(
  max_duration*(1-empty_batch[ma,ba]) >= duration[ma,ba]
);
%4
constraint forall (ma in MACHINES, ba in 1..n)(
  a*(1-empty_batch[ma,ba]) >= attribute_for_batch[ma,ba]
);
%5
constraint forall (ma in MACHINES, ba in 1..n)(
  empty_batch[ma,ba] <= batch_in_shift[ma,ba,s+1]
);

%batch may not start before earliest_start of jobs in batch
constraint forall (ma in MACHINES, ba in 1..n, j in 1..n)(
  start_times[ma,ba] >= earliest_start[j]*job_in_batch[ma,ba,j]
);

%batch duration is at least min_time[j] and at most max_time[j] for every job j in batch
constraint forall (ma in MACHINES, ba in 1..n, j in 1..n)(
  duration[ma,ba] >= min_time[j]*job_in_batch[ma,ba,j]
  /\
  duration[ma,ba] <= max_time[j]*job_in_batch[ma,ba,j] + max_duration*(1-job_in_batch[ma,ba,j])
);



%total batch size must be less than max machine capacity
constraint forall (ma in MACHINES, ba in 1..n)
(
  sum(j in 1..n)(size[j]*job_in_batch[ma,ba,j])  <= max_cap[ma]
);


%setup times and costs between batches
%setup_times_between_batches[i] is the setup time between batch i and the next batch
%setup_costs_between_batches[i] is the setup cost between batch i and the next batch
constraint forall (ma in MACHINES, ba in 1..n-1)(
  let {
    var ATTRIBUTES: attr1 = attribute_for_batch[ma,ba];
    var ATTRIBUTES: attr2 = attribute_for_batch[ma,ba+1];
  } in
  setup_times_between_batches[ma,ba]=setup_times_mod[attr1,attr2]
  /\
  setup_costs_between_batches[ma,ba]=setup_costs_mod[attr1,attr2]
);

% batches are sorted in ascending order of start times
% setup times must be considered in between batches
constraint forall (ma in MACHINES, ba in 1..n-1)(
    start_times[ma,ba+1]
    >=
    start_times[ma,ba]
    + duration[ma,ba]
    + setup_times_between_batches[ma,ba]
);

%every batch lies in exactly one shift
constraint forall (ma in MACHINES, ba in 1..n)(
  sum(j in 1..s+1)(batch_in_shift[ma,ba,j])=1
  );

%the starting time of a batch determines in which shift it lies
constraint forall (ma in MACHINES, ba in 1..n, j in 1..s+1)(
m_a_s_mod[ma,j] * batch_in_shift[ma,ba,j] <= start_times[ma,ba]
/\
start_times[ma,ba] <= m_a_e_mod[ma,j] * batch_in_shift[ma,ba,j] + l*(1-batch_in_shift[ma,ba,j])
);

%entire batch processing time and precceding setup time must lie within one shift
% %if batch_in_shift[ma,ba,j]=1 then start_times[ma,ba] - setup_times_between_batches[ma,ba-1] >=  m_a_s[ma,j]
constraint forall (ma in MACHINES, ba in 2..n, j in 1..s+1)(
  start_times[ma,ba] - setup_times_between_batches[ma,ba-1]
  >=
  m_a_s_mod[ma,j]*batch_in_shift[ma,ba,j]
);
%for first batch on machine:
%leave enough time for setup from initial state of machine
constraint forall (ma in MACHINES, j in 1..s+1)(
  start_times[ma,1] - setup_times_mod[initState[ma],attribute_for_batch[ma,1]]
  >=
  m_a_s_mod[ma,j]*batch_in_shift[ma,1,j]
);
% %if batch_in_shift[ma,ba,j]=1 then start_times[ma,ba] + duration[ma,ba] <=  m_a_e[ma,j]
constraint forall (ma in MACHINES, ba in 1..n, j in 1..s+1)(
  start_times[ma,ba] + duration[ma,ba]
  <=
  (1-batch_in_shift[ma,ba,j])*l + m_a_e_mod[ma,j]*batch_in_shift[ma,ba,j]

);


%late jobs
constraint forall (j in 1..n, ma in MACHINES, ba in 1..n)(
  late_job[j,ma,ba] <= job_in_batch[ma,ba,j]
);
constraint forall (j in 1..n, ma in MACHINES, ba in 1..n)(
  start_times[ma,ba] + duration[ma,ba] - latest_end[j]*(job_in_batch[ma,ba,j]) +late_job[j,ma,ba]*(latest_end[j]-l) <= (1-job_in_batch[ma,ba,j])*l
);
% constraint forall (j in 1..n, ma in MACHINES, ba in 1..n)(
%   start_times[ma,ba] + duration[ma,ba] +late_job[j,ma,ba]*(latest_end[j]-l) <= latest_end[j]
% );
constraint forall (j in 1..n, ma in MACHINES, ba in 1..n)(
  start_times[ma,ba] + duration[ma,ba] - latest_end[j] > (1-late_job[j,ma,ba])*(-l-1)
);


%%---------Objective--------------------------------------------------------------------------------------------------------------------------------------
var min_duration*a..running_time_bound: running_time_oven :: output_var;
running_time_oven = sum(ma in MACHINES, i in 1..n)(duration[ma, i]);

var 0..n: finished_too_late :: output_var;
finished_too_late =
    sum(j in 1..n, ma in MACHINES, ba in 1..n)(late_job[j,ma,ba]);



var 0..n*max_setup_cost: total_setup_costs :: output_var;
total_setup_costs =
  sum(setup_costs_between_batches)
  + %setup costs befor first batch
  sum(ma in MACHINES)
    (setup_costs_mod[initState[ma],attribute_for_batch[ma,1]]);

var 0..upper_bound_integer_objective: objective :: output_var;
objective =
  mult_factor_total_runtime * running_time_oven
  + mult_factor_finished_toolate * finished_too_late
  + mult_factor_total_setupcosts * total_setup_costs;

%%%%%--------Output---------------------------------------------------------------------------------------------------------------------------------------

%variables needed for output only
array[1..n] of var 1..n: batch_for_job; % :: output_only; %cannot be used vor variables, only for parameters
batch_for_job = array1d(1..n, [sum(ma in MACHINES, ba in 1..n)(job_in_batch[ma,ba,j]*ba)| j in 1..n]);
array[1..n] of var MACHINES: machine_for_job;
machine_for_job = array1d(1..n, [sum(ma in MACHINES, ba in 1..n)(job_in_batch[ma,ba,j]*ma)| j in 1..n]);

output ["objective = \(objective);\n",
"running_time_oven = \(running_time_oven);\n",
"total_setup_costs = \(total_setup_costs);\n",
"finished_too_late = \(finished_too_late);\n",
"late_job = \(late_job);\n",
%"Total number of batches: \(b);\n",
"Jobs are scheduled for following batches: \(batch_for_job);\n",
"Jobs are scheduled for following machines: \(machine_for_job);\n",
"Start times of batches are: \(start_times);\n",
"Durations of batches are: \(duration);\n",
"empty_batch: \(empty_batch)\n",
"Setup times between batches: \(setup_times_between_batches);\n",
"Setup costs between batches: \(setup_costs_between_batches);\n",
"Attribute of batch: \(attribute_for_batch);\n"
,"batch_in_shift: \(batch_in_shift)\n"
,"upper_bound_integer_objective: \(upper_bound_integer_objective);\n"
];

% autogenerated (accepted+proven): NoJobsOnIneligibleMach: Forbids assigning a job to any machine outside its eligibility set by forcing all corresponding job_in_batch variables to 0, which is logically implied by the two existing 'sum = 1' constraints over all machines and only eligible machines. Making this explicit prunes a large number of binary variables up front and strengthens propagation on job-machine assignments.
constraint (forall(j in 1..n, ma in MACHINES where not (ma in eligible_machine[j]))( sum(ba in 1..n)(job_in_batch[ma,ba,j]) = 0 ));

% autogenerated (candidate): ZeroSetupCostIfNeighborEmpty: Enforces that the setup cost between two consecutive batches is zero whenever at least one of them is empty, which follows from attribute_for_batch being 0 for empty batches and the definition of setup_costs_mod. This gives a direct propagation path from empty_batch to setup_costs_between_batches and then to the objective.
constraint (forall(ma in MACHINES, ba in 1..n-1)( setup_costs_between_batches[ma,ba] <= max_setup_cost * (1 - empty_batch[ma,ba]) * (1 - empty_batch[ma,ba+1]) )) ::redundant;

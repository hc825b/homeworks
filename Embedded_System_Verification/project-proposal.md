### Project Goal

Our project goal is to infer failure condition for self-adaptive applications.
Self-adaptative applications continually sense their environments and make
adaptation according to their predefined logics, and forms a reaction loop.
Typically, developers write assertions or failure condtions over sensor
values checked at each reaction loop iteration. The assertions often describe
the danger zone where the application crashes and is hard to recover.
In this context, we want to infer another condition over sensor value impling the
violation of the assertions developers provided, but requires less iterations of
the loop to trigger.
Intuitively, the infered condition can be used to refine the predefined logic to
avoid trggering of the assertions.
Another benefit from this project is for simulation and testing.
Less iterations simply leads to less time usage for simulation and testing.

Our work will be based on verification and simulation framework as well as
model and definitions provided in [1].
The main challenges for this project is to infer and prove a new failure condtion
that provide the same power as a given assertion.
Additionally, we also consider the model of uncertainty in environment described
in [1], and the infered condition should preserve probability of violation on
assertions. 


### Problem Description

Given an Interactive State Machine *M* described in [1], a failure condition *fc*,
an environment model *E*, 
ideally we infer a new failure condition *fc'* such that,
for each possible counterexample *c* satisfying *fc* with iterations and probability, 
*c* satisfies *fc'* with the same probability but requires less iterations to trigger.

A heuristic version is to use a set of existing counterexamples *C* satisfying *fc*,
and we infer *fc'* such that each *c* in *C* satisfies *fc'* with the same probability
but shorter length.


### Milestones

+ Investigation  (2~3 weeks)
  - Collect example self-adaptive programs, models, and failure conditions
  - Collect counterexamples using tools provided by [1].
  - Propose algorithms or heuristics

+ Implementation (4~6 weeks)
  - Implement algorithm without uncertainty in environment model
  - Interim Report
  - Implement algorithm with uncertainty in environment model

+ Evaluation     (2~3 weeks)
  - Experiments
  - Final Report and presentation

### References

[1] Wenhua Yang, Chang Xu, Yepang Liu, Chun Cao, Xiaoxing Ma, and Jian Lu. 2014.
    "Verifying self-adaptive applications suffering uncertainty." ASE '14.

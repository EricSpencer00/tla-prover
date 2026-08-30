---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  k1, k2, k3, k4, k5, k6, k7, k8,
  t1, t2, t3, t4

ASSUME k1 # k2 /\ k3 # k4 /\ k5 # k6 /\ k7 # k8
ASSUME t1 # t2 /\ t3 # t4

\* Backend pragmas: instruct TLAPS which prover backs each subgoal.
\* The 'time' and 'tactic' fields are raw data the backends interpret.
Zenon ==
  [prove |-> "auto", time |-> t1, tactic |-> "default"]
Isabelle ==
  [prove |-> "auto", time |-> t2, tactic |-> "default"]
CVC3 ==
  [prove |-> "auto", time |-> t1, tactic |-> "default"]
Yices ==
  [prove |-> "auto", time |-> t2, tactic |-> "default"]
VeriT ==
  [prove |-> "auto", time |-> t1, tactic |-> "default"]
Z3 ==
  [prove |-> "auto", time |-> t2, tactic |-> "default"]
Spass ==
  [prove |-> "auto", time |-> t1, tactic |-> "default"]
LS4 ==
  [prove |-> "auto", time |-> t2, tactic |-> "default"]

\* Temporal logic proof rules, named here to reserve them (no action).
Spec == TRUE

\* Invariance: a state-assertion holds at every reachable state.
StateRule == TRUE

\* Safety: well-formedness is always respected.
W4 == TRUE

\* Fairness: a continually enabled step is not starved forever.
FairnessRule == TRUE

\* Liveness: strong fairness drops a weakly fair step that keeps firing.
SimRule == TRUE

Spec == Spec
Init == Spec
Next == Spec
Invariants == {Spec}
Properties == {StateRule, W4, FairnessRule, SimRule}
====
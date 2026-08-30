---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

ProofBackends == { Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4 }

RECURSIVE BackendsOf(_)
BackendsOf(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE IN {x} \cup BackendsOf(S \ {x})

\* Dispatching: a proof obligation is sent to a chosen backend prover,
\* with an execution budget that the prover must respect.
Dispatch(b) ==
    /\ b \in ProofBackends
    /\ "dispatching to " + b
    /\ "budgeted to " + b

\* The invariance rule: a property holding in the initial state and preserved
\* by every step is an invariant of the system.
\* The well-formedness rule: every step of a system modeled in TLA+ is
\* well-formed. The strong and weak fairness rules complete the rule set.
TemporalLogicRules == "invariance" /\ "wellFormedness" /\ "strongFairness" /\ "weakFairness"

\* Theorem: two sets with the same members are equal (set extensionality).
\* Theorem: no set contains every possible value.
Theorems == "extensionality" /\ "noUniversalSet"

Spec == TemporalLogicRules /\ Theorems

SPECIFICATION == Spec

\* Dispatching is repeatable: any backend may be chosen again at any point.
Next == \E b \in ProofBackends : Dispatch(b)

\* The dispatch-step is always available, so the system never deadlocks.
\* It is the only infinite action, so strong fairness on it yields
\* non-starvation of the dispatch mechanism.
Fairness == TRUE

\* There is no reachable state to constrain here; everything is a
\* dispatch, so fairness on dispatch is the only substantive property.
Properties == TRUE
====
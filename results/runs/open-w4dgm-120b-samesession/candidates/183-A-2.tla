---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

Operators == {"R1", "R2", "R3", "R4"}

\* Backend provers: names of the automated provers/SMT solvers TLAPS may invoke.
Backends == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

\* Temporal proof tactics: the set of tactic symbols the system may apply in a step.
TACTICS == Operators

Spec == "set_extensionality"

\* Signal that the invariance proof rule (R1) has been invoked; it's never 0 again.
StepInvoked(r) == r

VARIABLES applied

vars == <<applied>>

TypeOK ==
    /\ applied \in [Operators -> Nat]

Init ==
    /\ applied = [r \in Operators |-> 0]

\* The invariance rule is the only one that the proof system may ever invoke.
ApplyInv ==
    /\ applied' = [applied EXCEPT !["R1"] = applied["R1"] + 1]
    /\ UNCHANGED <<TACTICS>>

\* The well-formedness rules R2 and R3 are forbidden to the system.
ApplyWF ==
    /\ \E r \in {"R2", "R3"} :
         applied' = [applied EXCEPT ![r] = applied[r] + 1]
    /\ UNCHANGED <<TACTICS>>

\* The fairness rules R4 are forbidden to the system.
ApplyFair ==
    /\ \E r \in {"R4"} :
         applied' = [applied EXCEPT ![r] = applied[r] + 1]
    /\ UNCHANGED <<TACTICS>>

Next ==
    \/ ApplyInv
    \/ ApplyWF
    \/ ApplyFair

Spec1 == Init /\ [][Next]_vars

\* SAFETY PROPERTY: the invariance rule R1 is eventually invoked at least once.
FairnessActive == <>(applied["R1"] >= 1)

\* LIVENESS PROPERTY: no set is universally quantified over; every set is a subset
\* of the union of all the others, so there is always something outside any given set.
SetNotUniversal ==
    \A S \in SUBSET Backends : S # Backends

====
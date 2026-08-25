---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

\*--- Finite version of Nat for model checking -----------------
NatOverride == 0 .. MaxNat

\*--- State constraint: keep all ticket numbers below MaxNat ----
StateConstraint ==
    /\ \A i \in Proc: ticket[i] < MaxNat

\*--- Specification (inherit Init and Next, add the constraint)----
Spec == (Init /\ StateConstraint) /\ [] [Next /\ StateConstraint]_vars

====
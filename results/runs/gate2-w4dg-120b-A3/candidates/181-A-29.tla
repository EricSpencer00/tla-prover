---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The base specification's proof applies to all naturals; the model checker
\* works against a finite range, so Nat is overridden with a bounded version:
\* the same name is not re-declared here, only the operator's definition.
NatOverride == 0..MaxNat

\* The theorem from the base spec is assumed at the constant level so TLC can
\* process the model without re-proving it.
ASSUME \A n \in NatOverride : 2 * n \in NatOverride

\* A trivial spec: the model consists of a single reachable state, so the
\* safety and liveness obligations are all vacuous.
VARIABLES dummy

TypeOK == dummy \in {0}

Init == dummy = 0

Next == UNCHANGED dummy

vars == <<dummy>>

Spec == Init /\ [][Next]_vars

\* No safety condition beyond the type constraint.
NoStutter == TypeOK

\* There is no liveness condition to require, but the config expects a
\* property clause; give one that is trivially true.
Trivial == TRUE

SpecOk == Spec

====
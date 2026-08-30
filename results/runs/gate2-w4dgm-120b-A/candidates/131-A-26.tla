---- MODULE MajorityProof ----
EXTENDS Majority, Integers, FiniteSets

CONSTANTS Value

\* No new state variables: everything is inherited from Majority.

TypeOK ==
    /\ candidates \subseteq Value
    /\ seen \in 0..N
    /\ pos \in 0..N
    /\ candidate \in Value

\* The invariant from Majority, plus type-checking on the whole state.
Correct ==
    /\ Inv
    /\ candidates \subseteq Value
    /\ seen \in 0..N
    /\ pos \in 0..N
    /\ candidate \in Value

Init ==
    /\ Majority.Init
    /\ candidate \in Value

Vote(v) ==
    /\ Majority.Vote(v)
    /\ candidates' = candidates \cup {v}
    /\ UNCHANGED <<seen, pos, candidate>>

Next ==
    \/ \E v \in Value : Vote(v)
    \/ Majority.Next

Spec == Init /\ [][Next]_<<candidates, seen, pos, candidate>>

\* No liveness properties for this module.
====
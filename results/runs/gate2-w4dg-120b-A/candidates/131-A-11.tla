---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences, MajorityVote

CONSTANTS Value

\* The specification is the full majority vote algorithm from MajorityVote.
Spec == Spec

TypeOK ==
    /\ seq \in Seq(Value)
    /\ candidate \in Value
    /\ count \in 0 .. Len(seq)
    /\ index \in 0 .. Len(seq)

Init == Init

Next == Next

\* No new state: the invariant is proved against the base spec only.
Inv == Inv

Correct ==
    /\ Inv
    /\ \A e \in Value :
        (Occurs(e, 1, index) > index / 2) => (e = candidate)

====
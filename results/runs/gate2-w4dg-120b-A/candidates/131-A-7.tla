---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

\* Imports the main Boyer-Moore majority vote specification and re-exports its
\* operators so the proof can be written against them directly.
EXTENDS Majority

CONSTANT Value

TypeOK ==
    /\ Value \in 1..1
    /\ Majority.TypeOK

Inv ==
    /\ Majority.Inv
    /\ \A i \in 0..(Majority.N - 1) : i \in Majority.positions

Spec ==
    /\ Majority.Spec
    /\ \A i \in 0..(Majority.N - 1) : i \in Majority.positions

Init ==
    /\ Majority.Init
    /\ \A i \in 0..(Majority.N - 1) : i \in Majority.positions

Next ==
    /\ Majority.Next
    /\ \A i \in 0..(Majority.N - 1) : i \in Majority.positions

Correct == Majority.Correct

====
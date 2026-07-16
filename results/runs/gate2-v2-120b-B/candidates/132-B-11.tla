---- MODULE MCMajority -----------------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS bound, A, B, C
ASSUME bound \in Nat \ {0}

Value == {A, B, C}
BoundedSeq(S) == \E n \in 0..bound : [1..n -> S]

VARIABLES seq, i, cand, cnt

\* -----------------------------------------------------------------
\* Majority Interface (minimal definition required for this module)
\* -----------------------------------------------------------------
MajorityInit == cand = Null \cup Value
MajorityStep == 
    /\ i \in 0..bound
    /\ IF i = 0 THEN cand' = Null /\ cnt' = 0
       ELSE 
          LET x == seq[i] IN
          IF cnt = 0 THEN cand' = x /\ cnt' = 1
          ELSE IF x = cand THEN cand' = cand /\ cnt' = cnt + 1
          ELSE cand' = cand /\ cnt' = cnt - 1
    /\ UNCHANGED <<seq>>

\* -----------------------------------------------------------------
\* Model variables and initialization
\* -----------------------------------------------------------------
Init ==
    /\ seq = {}
    /\ i = 0
    /\ cand \in Null \cup Value
    /\ cnt \in Nat
    /\ MajorityInit

\* -----------------------------------------------------------------
\* Step relation
\* -----------------------------------------------------------------
Next ==
    \/ /\ i < bound
       /\ i' = i + 1
       /\ seq' = [seq EXCEPT ![i'] = Value[RandomElement[Value]]]
       /\ MajorityStep
    \/ /\ i = bound
       /\ UNCHANGED <<seq, i, cand, cnt>>

\* -----------------------------------------------------------------
\* Safety Property: if a majority exists, cand equals that element
\* -----------------------------------------------------------------
MajorityProp ==
    \A e \in Value :
        (Cardinality({j \in 1..bound : seq[j] = e}) > bound / 2) => cand = e

\* -----------------------------------------------------------------
\* Invariant (same as safety property for TLC checking)
\* -----------------------------------------------------------------
Inv == MajorityProp

\* -----------------------------------------------------------------
\* The overall specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

====
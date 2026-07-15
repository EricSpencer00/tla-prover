---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS A, B, C, bound
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

Init ==
    /\ seq = {}
    /\ i = 0
    /\ cand = {}
    /\ cnt = 0

Next ==
    \/ /\ i < bound
       /\ i' = i + 1
       /\ \E x \in Value :
            /\ seq' = [seq EXCEPT ![i'] = x]
            /\ IF cnt = 0
                 THEN cand' = x
                 ELSE cand' = cand
            /\ IF cnt = 0
                 THEN cnt' = 1
                 ELSE IF x = cand
                         THEN cnt' = cnt + 1
                         ELSE cnt' = cnt - 1
    \/ /\ i = bound
       /\ UNCHANGED <<seq, i, cand, cnt>>

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

Terminating == i = bound

End == /\ seq \in BoundedSeq(Value)
       /\ Terminating
       /\ cand \in Value
       /\ \A v \in Value : 
            (Cardinality({j \in 1..Len(seq) : seq[j] = v}) > Len(seq) / 2) => v = cand

=============================================================================
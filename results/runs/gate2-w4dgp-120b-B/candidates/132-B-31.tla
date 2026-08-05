---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound
ASSUME bound \in Nat

Value == {A, B, C}

VARIABLES seq, i, cand, cnt

Init ==
    /\ seq = << >>
    /\ i = 0
    /\ cand = "\#"
    /\ cnt = 0

Push(e) ==
    /\ i < bound
    /\ i' = i + 1
    /\ seq' = Append(seq, e)
    /\ UNCHANGED <<cand, cnt>>

Vote ==
    /\ i > 0
    /\ cnt' = IF seq[i] = cand THEN cnt + 1 ELSE IF cnt = 0 THEN 1 ELSE cnt - 1
    /\ cand' = IF cnt = 0 \/ seq[i] = cand THEN seq[i] ELSE cand
    /\ UNCHANGED <<seq, i>>

Quiet ==
    /\ i = bound
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next ==
    \/ \E e \in Value : Push(e)
    \/ Vote
    \/ Quiet

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

Bump ==
    /\ \A k \in DOMAIN seq : seq[k] = A
    /\ i < bound
    /\ Push(A)

MajorityHolds ==
    (cnt > 0) ~> (cand = A)
====
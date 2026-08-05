---- MODULE MCMajority -----------------------------------------------------------------
EXTENDS Integers, FiniteSets
CONSTANTS A, B, C
ASSUME A # B /\ B # C /\ A # C

Value == {A, B, C}

vars == <<seq, i, cand, cnt>>

Init ==
    /\ seq = <<A, B, A>>
    /\ i = 1
    /\ cand = "none"
    /\ cnt = 0

Bump ==
    /\ i < 4
    /\ i' = i + 1
    /\ cand' = IF cnt = 0 THEN seq[i] ELSE IF seq[i] = cand THEN cand ELSE "none"
    /\ cnt' = IF cnt = 0 \/ seq[i] = cand THEN cnt + 1 ELSE cnt - 1

Done ==
    /\ i = 4
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == Bump \/ Done
Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ seq \in [1..3 -> Value]
    /\ i \in 1..4
    /\ cand \in Value \cup {"none"}
    /\ cnt \in 0..3

BoundedDom ==
    \A k \in DOMAIN seq : k <= 3

=============================================================================
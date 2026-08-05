---- MODULE MCMajority ----
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \in Nat

Value == {A,B,C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

Init ==
    /\ seq = << >>
    /\ i = 0
    /\ cand = 0
    /\ cnt = 0

Append(x) ==
    /\ i < bound
    /\ seq' = Append(seq, x)
    /\ i' = i + 1
    /\ UNCHANGED <<cand, cnt>>

Vote(x) ==
    /\ i > 0
    /\ UNCHANGED <<seq, i>>
    /\ IF cnt = 0 \/ cand = x
         THEN /\ cand' = x
              /\ cnt' = IF cnt = 0 THEN 1 ELSE cnt + 1
         ELSE /\ cand' = cand
              /\ cnt' = cnt - 1

Next ==
    \/ \E x \in Value : Append(x)
    \/ \E x \in Value : Vote(x)

vars == <<seq, i, cand, cnt>>

StateConstraint == i <= bound

Spec == Init /\ [][Next]_vars

MajorityFound ==
    \A x \in Value :
        (\A k \in (DOMAIN seq) : seq[k] = x) => (i >= 1 /\ cand = x)

====
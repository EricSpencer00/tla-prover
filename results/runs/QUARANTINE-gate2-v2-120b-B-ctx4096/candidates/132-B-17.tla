---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS A, B, C, bound

\* Ensure that 'bound' is a natural number (including 0) so that bounded sequences are well‑defined.
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

Init ==
    /\ seq = <<>>
    /\ i = 0
    /\ cand \in Value
    /\ cnt = 0

Next ==
    \/ /\ i < bound
       /\ i' = i + 1
       /\ LET e == CHOOSE x \in Value : TRUE IN
          /\ seq' = Append(seq, e)
          /\ IF cnt = 0
                THEN /\ cand' = e
                     /\ cnt' = 1
                ELSE IF e = cand
                        THEN /\ cand' = cand
                             /\ cnt' = cnt + 1
                        ELSE /\ cand' = cand
                             /\ cnt' = cnt - 1
    \/ /\ i = bound
       /\ UNCHANGED <<seq, i, cand, cnt>>

\* The specification consists of the initial predicate and the next‑state relation.
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Safety invariant: the candidate always belongs to the set of possible values.
Inv == cand \in Value

=============================================================================
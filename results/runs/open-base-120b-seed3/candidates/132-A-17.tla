---- MODULE MCMajority ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS A, B, C, bound

\* Set of possible element values
V == {A, B, C}

\* Finite sequences of length at most **bound** over a set S
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

\* Initial state
Init ==
    /\ seq \in BoundedSeq(V)
    /\ i = 1
    /\ cand \in V
    /\ cnt = 0

\* Scan the next element according to the Boyer‑Moore rules
Scan ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
         IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt' = 1
         ELSE IF cand = x THEN
              /\ cand' = cand
              /\ cnt' = cnt + 1
         ELSE
              /\ cand' = cand
              /\ cnt' = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

\* Overall next‑state relation (allow stuttering)
Next ==
    \/ Scan
    \/ UNCHANGED <<seq, i, cand, cnt>>

\* Full specification
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq(V)
    /\ i \in Nat
    /\ cand \in V
    /\ cnt \in Nat

\* Correctness: after a complete scan, any true majority element must equal the candidate
Correct ==
    (i > Len(seq)) =>
        \A v \in V :
            ( Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2 )
                => v = cand

\* Simple inductive invariant used for verification
Inv ==
    /\ cnt \in Nat
    /\ i \in 1..(Len(seq) + 1)

====
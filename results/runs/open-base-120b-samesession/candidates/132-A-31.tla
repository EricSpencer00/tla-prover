---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* Distinct model values
ASSUME A /= B /\ A /= C /\ B /= C

\* Set of possible element values
Values == { A, B, C }

\* Finite version of Seq limited by the bound
BoundedSeq(V) == { s \in Seq(V) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

\* Initial state
Init ==
    /\ seq \in BoundedSeq(Values)
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

\* One step of the Boyer‑Moore scan
Next ==
    \/ /\ i <= Len(seq)
       /\ LET e == seq[i] IN
          IF cnt = 0 THEN
              /\ cand' = e
              /\ cnt'  = 1
          ELSE IF e = cand THEN
              /\ cand' = cand
              /\ cnt'  = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt'  = cnt - 1
       /\ i' = i + 1
       /\ UNCHANGED <<seq>>
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

\* Variable tuple for stuttering
vars == <<seq, i, cand, cnt>>

\* Full specification
Spec == Init /\ [][Next]_vars

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

\* Correctness property: any true majority element equals the final candidate
Correct ==
    /\ i > Len(seq)
    => \A v \in Values :
          ( Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2 )
          => v = cand

\* Inductive invariant of the Boyer‑Moore algorithm
Inv ==
    /\ i <= Len(seq) + 1
    /\ cnt = 2 * Cardinality({ j \in 1..(i-1) : seq[j] = cand }) - (i - 1)

====
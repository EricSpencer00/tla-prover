---- MODULE MCMajority ----
EXTENDS Sequences, FiniteSets, Naturals

CONSTANTS A, B, C, bound

\* The set of possible element values
Val == { A, B, C }

\* BoundedSeq(n) is the set of all sequences over Val of length n
BoundedSeq(n) == { s \in Seq(Val) : Len(s) = n }

VARIABLES seq, len, pos, cand, cnt

\* Initial state
Init ==
    /\ len \in 0..bound
    /\ seq \in BoundedSeq(len)
    /\ pos = 1
    /\ cnt = 0
    /\ cand \in Val

\* One step of the Boyer‑Moore scan
Next ==
    \/ /\ pos <= len
       /\ LET x == seq[pos] IN
          IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt' = 1
          ELSE IF x = cand THEN
              /\ cand' = cand
              /\ cnt' = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt' = cnt - 1
       /\ pos' = pos + 1
       /\ UNCHANGED <<seq, len>>
    \/ /\ pos > len
       /\ UNCHANGED <<seq, len, pos, cand, cnt>>

\* The full specification
Spec == Init /\ [][Next]_<<seq, len, pos, cand, cnt>>

\* Type correctness invariant
TypeOK ==
    /\ len \in 0..bound
    /\ seq \in BoundedSeq(len)
    /\ pos \in 1..len+1
    /\ cand \in Val
    /\ cnt \in Nat

\* Helper: count occurrences of v in the first n positions of seq
Count(v, s, n) == Cardinality({ i \in 1..n : s[i] = v })

\* Set of elements that are a strict majority in the whole sequence
MajoritySet == { v \in Val : Count(v, seq, len) > len / 2 }

\* Correctness: if a majority exists, cand must be that element
Correct == (MajoritySet = {} \/ cand \in MajoritySet)

\* Inductive invariant (placeholder)
Inv == TRUE

====
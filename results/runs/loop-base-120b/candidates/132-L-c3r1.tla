---- MODULE MCMajority ----
EXTENDS Sequences

CONSTANTS A, B, C, bound

\* The set of possible element values
Val == {A, B, C}

\* BoundedSeq(n) is the set of all sequences over Val of length n
BoundedSeq(n) == { s \in Seq(Val) : Len(s) = n }

VARIABLES seq, Len, pos, cand, cnt

\* Initial state
Init ==
    /\ Len \in 0..bound
    /\ seq \in BoundedSeq(Len)
    /\ pos = 1
    /\ cnt = 0
    /\ cand \in Val

\* One step of the Boyer‑Moore scan
Next ==
    \/ /\ pos <= Len
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
       /\ UNCHANGED <<seq, Len>>
    \/ /\ pos > Len
       /\ UNCHANGED <<seq, Len, pos, cand, cnt>>

\* The full specification
Spec == Init /\ [][Next]_<<seq, Len, pos, cand, cnt>>

\* Type correctness invariant
TypeOK ==
    /\ Len \in 0..bound
    /\ seq \in BoundedSeq(Len)
    /\ pos \in 1..Len+1
    /\ cand \in Val
    /\ cnt \in Nat

\* Helper: count occurrences of v in the first n positions of seq
Count(v, s, n) == Cardinality({ i \in 1..n : s[i] = v })

\* Set of elements that are a strict majority in the whole sequence
MajoritySet == { v \in Val : Count(v, seq, Len) > Len / 2 }

\* Correctness: if a majority exists, cand must be that element
Correct == (MajoritySet = {} \/ cand \in MajoritySet)

\* Inductive invariant (trivial placeholder)
Inv == TRUE

====
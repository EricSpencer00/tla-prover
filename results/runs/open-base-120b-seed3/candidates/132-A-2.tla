---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* The set of possible element values
ValueSet == { A, B, C }

\* A finite version of Seq limited by the bound
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\* State variables
VARIABLES seq, i, cand, cnt

\* Helper definitions
CountSeq(s, v) == Cardinality({ j \in DOMAIN s : s[j] = v })
PrefixIdx == IF i = 1 THEN {} ELSE 1..(i - 1)

\* Invariant capturing the algorithmic invariant
Inv ==
  /\ cnt = Cardinality({ j \in PrefixIdx : seq[j] = cand })
       - Cardinality({ j \in PrefixIdx : seq[j] # cand })
  /\ cnt >= 0

\* Type correctness invariant
TypeOK ==
  /\ seq \in BoundedSeq(ValueSet)
  /\ i \in Nat
  /\ cand \in ValueSet
  /\ cnt \in Nat

\* Correctness property: after the scan is finished, any majority element must be the candidate
Correct ==
  (i > Len(seq)) => 
    \A v \in ValueSet :
      (CountSeq(seq, v) > Len(seq) / 2) => cand = v

\* Initial state
Init ==
  /\ seq \in BoundedSeq(ValueSet)
  /\ i = 1
  /\ cand \in ValueSet
  /\ cnt = 0

\* The main step of the Boyer‑Moore algorithm
Next ==
  \/ /\ i <= Len(seq)
     /\ LET x == seq[i] IN
        CASE
          cnt = 0 -> /\ cand' = x
                     /\ cnt' = 1
          x = cand -> /\ cand' = cand
                     /\ cnt' = cnt + 1
          OTHER   -> /\ cand' = cand
                     /\ cnt' = cnt - 1
        END CASE
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ i > Len(seq)
     /\ UNCHANGED <<seq, i, cand, cnt>>

\* Specification
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Exported identifiers required by the .cfg file
SPECIFICATION Spec
INVARIANTS TypeOK, Correct, Inv

====
---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* The set of possible element values
ValueSet == { A, B, C }

\* Bounded sequences over a set S, with length at most `bound`
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i = 1
    /\ cnt = 0
    /\ cand \in ValueSet

\* ----------------------------------------------------------------------
\* One step of the Boyer‑Moore majority vote algorithm
\* ----------------------------------------------------------------------
Scan ==
    /\ i <= Len(seq)
    /\ LET cur == seq[i] IN
       IF cnt = 0 THEN
          /\ cand' = cur
          /\ cnt' = 1
          /\ i' = i + 1
       ELSE IF cur = cand THEN
          /\ cand' = cand
          /\ cnt' = cnt + 1
          /\ i' = i + 1
       ELSE
          /\ cand' = cand
          /\ cnt' = cnt - 1
          /\ i' = i + 1
    /\ seq' = seq

\* Stuttering after the scan is finished
Stutter ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == Scan \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Count(v, s) == Cardinality({ j \in 1..Len(s) : s[j] = v })

Majority(v, s) == Count(v, s) > Len(s) / 2

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

\* The main correctness property: any true majority element must equal the
\* candidate after the whole sequence has been scanned.
Correct ==
    (i > Len(seq)) => 
        \A v \in ValueSet : (Majority(v, seq) => cand = v)

\* An inductive invariant (here we reuse TypeOK and state that cnt is natural)
Inv == TypeOK

====
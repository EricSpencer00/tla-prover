---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* --- Value set -------------------------------------------------
ValueSet == { A, B, C }

\* --- Bounded sequences (finite version of Seq) -----------------
BoundedSeq == 
  UNION { [i \in 1..n |-> v] : 
          n \in 0..bound,
          v \in [1..n -> ValueSet] }

\* --- Helper functions -------------------------------------------
Len(s) == 
  IF s = {} THEN 0 ELSE Max(DOMAIN s)

Count(s, v) == 
  Cardinality({ j \in DOMAIN s : s[j] = v })

\* --- State variables --------------------------------------------
VARIABLES seq, i, cand, cnt

\* --- Initial state -----------------------------------------------
Init == 
  /\ seq \in BoundedSeq
  /\ i = 1
  /\ cnt = 0
  /\ cand \in ValueSet

\* --- Next-state relation -----------------------------------------
Next == 
  \/ /\ i <= Len(seq)
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
  \/ /\ i > Len(seq)
     /\ UNCHANGED <<seq, i, cand, cnt>>

\* --- Specification ------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* --- Invariants --------------------------------------------------
TypeOK == 
  /\ seq \in BoundedSeq
  /\ i \in Nat
  /\ cand \in ValueSet
  /\ cnt \in Nat
  /\ i <= Len(seq) + 1

Inv == 
  /\ cnt \in Nat
  /\ (cnt = 0 => TRUE)
  /\ (cnt > 0 => cand \in ValueSet)

Correct == 
  /\ i = Len(seq) + 1
  /\ \A m \in ValueSet :
        (Count(seq, m) > Len(seq) / 2) => m = cand

\* --- Exported identifiers -----------------------------------------
SPECIFICATION == Spec
INVARIANTS == TypeOK, Correct, Inv

====
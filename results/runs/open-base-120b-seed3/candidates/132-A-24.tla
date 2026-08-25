---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* ----------------------------------------------------------------------
\* Bounded sequences over a set S, with length at most **bound**.
\* ----------------------------------------------------------------------
BoundedSeq(S) == 
  { f \in [Nat -> S] : 
      \E n \in 0..bound : DOMAIN f = 1..n }

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Values == {A, B, C}

Len(s) == 
  IF DOMAIN s = {} 
    THEN 0 
    ELSE Max(DOMAIN s)

Count(s, v) == 
  Cardinality({ j \in DOMAIN s : s[j] = v })

Majority(s) == 
  \E v \in Values : Count(s, v) > Len(s) / 2

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
  /\ seq \in BoundedSeq(Values)
  /\ i = 1
  /\ cnt = 0
  /\ cand \in Values

\* ----------------------------------------------------------------------
\* Transition relation (Boyer‑Moore scan)
\* ----------------------------------------------------------------------
Next == 
  \/ /\ i <= Len(seq)
     /\ LET x == seq[i] IN
        \/ /\ cnt = 0
           /\ cnt' = 1
           /\ cand' = x
           /\ i' = i + 1
        \/ /\ cnt > 0 /\ cand = x
           /\ cnt' = cnt + 1
           /\ cand' = cand
           /\ i' = i + 1
        \/ /\ cnt > 0 /\ cand # x
           /\ cnt' = cnt - 1
           /\ cand' = cand
           /\ i' = i + 1
  \/ /\ i > Len(seq)          \* scan finished – stutter
     /\ UNCHANGED <<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [] [Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK == 
  /\ seq \in BoundedSeq(Values)
  /\ i \in Nat
  /\ i >= 1
  /\ cand \in Values
  /\ cnt \in Nat

Correct == 
  /\ i > Len(seq)
  /\ Majority(seq)
  => \E v \in Values :
        cand = v /\ Count(seq, v) > Len(seq) / 2

Inv == cnt >= 0

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
=============================
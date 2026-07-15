---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound, Seq

\* ----------------------------------------------------------------------
\* Concrete value set
\* ----------------------------------------------------------------------
Vals == { A, B, C }

\* ----------------------------------------------------------------------
\* Bounded sequences of length at most 'bound' over Vals
\* ----------------------------------------------------------------------
BoundedSeqs == { s \in Seq(Vals) : Len(s) <= bound }

\* ----------------------------------------------------------------------
\* State variables (inherited from the main specification)
\* ----------------------------------------------------------------------
VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in BoundSeqs
  /\ pos \in Nat
  /\ cnt \in Nat
  /\ cand \in Vals

\* ----------------------------------------------------------------------
\* Initial state (as described)
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in BoundSeqs
  /\ pos = 1
  /\ cand \in Vals
  /\ cnt = 0

\* ----------------------------------------------------------------------
\* The three‑case scan step of the Boyer‑Moore algorithm
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pos <= Len(seq)
     /\ LET cur == seq[pos] IN
        IF cnt = 0 THEN
          /\ cand' = cur
          /\ cnt'  = 1
        ELSE IF cand = cur THEN
          /\ cand' = cand
          /\ cnt'  = cnt + 1
        ELSE
          /\ cand' = cand
          /\ cnt'  = cnt - 1
     /\ pos' = pos + 1
  \/ /\ pos > Len(seq)   \* the scan has finished; stutter forever
     /\ UNCHANGED <<seq, pos, cand, cnt>>

Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Safety property: any true majority element must equal the final candidate
\* ----------------------------------------------------------------------
Correct ==
  LET maj == { v \in Vals : Cardinality({ i \in 1..Len(seq) : seq[i] = v }) > Len(seq) / 2 } IN
    IF maj = {} THEN TRUE ELSE cand \in maj

\* ----------------------------------------------------------------------
\* Invariant (can be any useful property; here we reuse TypeOK)
\* ----------------------------------------------------------------------
Inv == TypeOK

\* ----------------------------------------------------------------------
\* The specification name required by the .cfg file
\* ----------------------------------------------------------------------
Spec == Spec

====
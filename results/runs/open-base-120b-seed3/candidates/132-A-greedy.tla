---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* ----------------------------------------------------------------------
\* BoundedSeq: a finite version of Seq, limited to length at most bound
\* ----------------------------------------------------------------------
BoundedSeq(S) == 
  UNION { [1..i -> S] : i \in 0..bound }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Values == {A, B, C}

LenSeq == Len(seq)

Majority(e) == 
  Cardinality({ i \in 1..LenSeq : seq[i] = e }) > LenSeq / 2

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK == 
  /\ seq \in BoundedSeq(Values)
  /\ pos \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Inductive invariant (can be strengthened later)
\* ----------------------------------------------------------------------
Inv == TypeOK

\* ----------------------------------------------------------------------
\* Correctness property: any true majority element must equal the final candidate
\* ----------------------------------------------------------------------
Correct == 
  (pos > LenSeq) => 
    \A e \in Values : Majority(e) => e = cand

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ cnt = 0
  /\ cand \in Values

\* ----------------------------------------------------------------------
\* Next-state relation (scan one element)
\* ----------------------------------------------------------------------
Next == 
  /\ pos <= LenSeq
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN
         /\ cand' = x
         /\ cnt' = 1
       ELSE IF cand = x THEN
         /\ cand' = cand
         /\ cnt' = cnt + 1
       ELSE
         /\ cand' = cand
         /\ cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<seq, pos, cand, cnt>>

Spec == Init /\ [][Next]_vars /\ WF_pos(Next)

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INVARIANTS == TypeOK, Correct, Inv

====
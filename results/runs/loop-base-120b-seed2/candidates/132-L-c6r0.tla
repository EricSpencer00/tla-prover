---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* ----------------------------------------------------------------------
\* Value set
\* ----------------------------------------------------------------------
Values == { A, B, C }

\* ----------------------------------------------------------------------
\* Bounded sequences over a set S (finite version of Seq)
\* ----------------------------------------------------------------------
BoundedSeq(S) == { s : \E n \in 0..bound : s \in [1..n -> S] }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Count(s, v) == Cardinality({ i \in DOMAIN s : s[i] = v })

MajorityExists(s) == \E v \in Values : Count(s, v) > Len(s) / 2

Majority(s) == CHOOSE v \in Values : Count(s, v) > Len(s) / 2

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Inductive invariant
\* ----------------------------------------------------------------------
Inv ==
  /\ cnt >= 0
  /\ cnt = Cardinality({ i \in 1..pos-1 : seq[i] = cand })
       - Cardinality({ i \in 1..pos-1 : seq[i] # cand })

\* ----------------------------------------------------------------------
\* Correctness property (majority element, if any, equals final candidate)
\* ----------------------------------------------------------------------
Correct ==
  MajorityExists(seq) => cand = Majority(seq)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

\* ----------------------------------------------------------------------
\* Scanning action (Boyer-Moore majority vote step)
\* ----------------------------------------------------------------------
Scan ==
  /\ pos <= Len(seq)
  LET x == seq[pos] IN
    /\ cand' = IF cnt = 0 THEN x ELSE cand
    /\ cnt'  = IF cnt = 0 THEN 1
               ELSE IF cand = x THEN cnt + 1
               ELSE cnt - 1
    /\ pos'  = pos + 1
    /\ UNCHANGED seq

\* ----------------------------------------------------------------------
\* Stutter after the scan is finished
\* ----------------------------------------------------------------------
Stutter ==
  /\ pos > Len(seq)
  /\ UNCHANGED <<seq, pos, cand, cnt>>

Next == Scan \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* The .cfg refers to the specification as "Spec", and to the invariants
\* as TypeOK, Correct, and Inv.
\* ----------------------------------------------------------------------
====
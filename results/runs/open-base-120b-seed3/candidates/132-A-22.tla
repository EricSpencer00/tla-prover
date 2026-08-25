---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* The set of possible element values
Values == { A , B , C }

\* Finite sequences over Values whose length does not exceed the bound
BoundedSeq == { s \in Seq(Values) : Len(s) \leq bound }

VARIABLES seq, pos, cand, cnt

vars == << seq , pos , cand , cnt >>

\* ---------- Initialization ----------
Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

\* ---------- Next-state relation ----------
Next ==
    \/ /\ pos \leq Len(seq)
       /\ LET x == seq[pos] IN
          IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt'  = 1
          ELSE IF cand = x THEN
              /\ cand' = cand
              /\ cnt'  = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt'  = cnt - 1
       /\ pos' = pos + 1
    \/ /\ pos > Len(seq)
       /\ UNCHANGED << seq , pos , cand , cnt >>

\* ---------- Specification ----------
Spec == Init /\ [][Next]_vars

\* ---------- Helper definitions ----------
Count(v) == Cardinality({ i \in 1..Len(seq) : seq[i] = v })

MajoritySet == { v \in Values : Count(v) > Len(seq) / 2 }

\* ---------- Invariants ----------
TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

Correct ==
    /\ MajoritySet # {}
    => cand \in MajoritySet

Inv ==
    /\ TypeOK
    /\ cnt \leq Len(seq)

====
---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Vals == {A, B, C}

\* A bounded version of Seq: only sequences up to the configured bound.
BoundedSeq == { s \in Seq(Vals) : Len(s) <= bound }

VARIABLES seq, p, cand, cnt

vars == <<seq, p, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ p \in 1..(Len(seq) + 1)
  /\ cand \in Vals
  /\ cnt \in 0..bound

Init ==
  /\ seq \in BoundedSeq
  /\ p = 1
  /\ cand \in Vals
  /\ cnt = 0

\* Scan the next element: adopt it as candidate, increment the counter,
\* or decrement the counter -- the three cases of Boyer-Moore.
Next ==
  \/ /\ p <= Len(seq)
     /\ IF seq[p] = cand
          THEN cand' = cand /\ cnt' = cnt + 1
          ELSE IF cnt = 0
                 THEN cand' = seq[p] /\ cnt' = 1
                 ELSE cand' = cand /\ cnt' = cnt - 1
     /\ p' = p + 1
  \/ /\ p > Len(seq)
     /\ p' = p
     /\ cand' = cand
     /\ cnt' = cnt
  /\ seq' = seq

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* After a full scan, any true majority must equal the surviving candidate.
Correct ==
  \A x \in Vals :
    (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) =>
      (x = cand)

Inv ==
  \A x \in Vals :
    (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) =>
      (x = cand)

Complete == p = Len(seq) + 1

SpecComplete == Spec /\ WF_vars(Next) /\ SF_vars(Next)

====
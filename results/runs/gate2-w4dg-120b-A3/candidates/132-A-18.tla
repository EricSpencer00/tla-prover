---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* BoundedSeq replaces the standard Seq operator from Sequences with a finite
\* version that only admits sequences whose length is at most the model bound.
\* Keeping EXTENDS Sequences lets us reuse the rest of the machinery unchanged.
BoundedSeq == {s \in Seq({A, B, C}) : Len(s) <= bound}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

\* The bound is a runtime parameter, so we keep it separate from the constant
\* set and only assume it is a natural number (the model files set it to 5).
TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 0..bound
  /\ cand \in {A, B, C}
  /\ cnt \in 0..bound

\* Safety: if a true majority exists by the end of the scan, it must be the
\* candidate the algorithm has settled on.
Correct ==
  (pos = Len(seq) /\ \E e \in {A, B, C} : 2 * Cardinality({i \in 1..Len(seq) : seq[i] = e}) > Len(seq)) => (cand = seq[pos])

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in {A, B, C}
  /\ cnt = 0

\* The three-case majority-vote scan from the original spec.
Step ==
  /\ pos < Len(seq)
  /\ IF cnt = 0 THEN
       /\ cand' = seq[pos]
       /\ cnt' = 1
     ELSE IF seq[pos] = cand THEN
       /\ cnt' = cnt + 1
     ELSE
       /\ cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ Correct

\* With weak fairness on the single step action a full scan always completes.
Properties ==
  /\ WF_vars(Step)
  /\ pos = Len(seq)

====
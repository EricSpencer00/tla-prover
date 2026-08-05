---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* The three distinct model values that can appear in sequences.
Elems == {A, B, C}

\* A bounded sequence operator: like Sequences!Seq but only for lengths up to
\* the checked bound (Seq is infinite, which TLC would not model-check).
BoundedSeq == {s \in [1 .. bound -> Elems] : TRUE}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1 .. (bound + 1)
  /\ cand \in Elems
  /\ cnt \in 0 .. bound

\* The inductive candidate is the true majority only after the whole scan.
Correct ==
  \A e \in Elems :
    (2 * Cardinality({i \in 1 .. Len(seq) : seq[i] = e}) > Len(seq))
      => (pos = Len(seq) + 1) => (cand = e)

\* The usual Boyer-Moore scan: a true majority can never be wiped out.
Inv ==
  \A i \in 1 .. Len(seq) :
    (cnt > 0) =>
      ((i < pos) => (seq[i] = cand))

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in Elems
  /\ cnt = 0

\* Scan the next element; the counter never drops below zero.
Step ==
  /\ pos <= Len(seq)
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

\* Exhaustive shuffling lets weak fairness reach the end of every reachable
\* scan, however late it starts or how often it is stalled.
WF_vars(Step)

====
---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

Values == {A, B, C}

BoundedSeq(dom) == {f \in [1 .. n -> dom] : n \in 0 .. bound}

VARIABLES seq, pos, cand, k

vars == <<seq, pos, cand, k>>

TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in 0 .. bound
  /\ cand \in Values
  /\ k \in Nat

Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ cand \in Values
  /\ k = 0

Scan ==
  /\ pos <= Len(seq)
  /\ IF k = 0 THEN
       /\ cand' = seq[pos]
       /\ k' = 1
     ELSE IF seq[pos] = cand THEN
       /\ k' = k + 1
       /\ cand' = cand
     ELSE
       /\ k' = k - 1
       /\ cand' = cand
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Scan]_vars

Correct ==
  \A e \in Values : (\A i \in 1 .. Len(seq) : seq[i] = e)
                     => (pos = Len(seq) + 1 /\ cand = e)

Inv ==
  \A e \in Values : (\A i \in 1 .. Len(seq) : seq[i] = e)
                     => (pos = Len(seq) + 1 /\ cand = e)

\* Fairness is strong here because Scan's applicability does not shrink while
\* it is applicable, so weak fairness lets it through any finite waiting chain.
Fairness == WF_vars(Scan)
====
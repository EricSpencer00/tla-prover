---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

SeqDom == UNION { [1 .. n -> Values] : n \in 0 .. bound }

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

BoundedSeq == SeqDom

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1 .. (bound + 1)
  /\ cand \in Values
  /\ count \in Nat

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in Values
  /\ count = 0

Scan ==
  /\ pos <= Len(seq)
  /\ LET v == seq[pos] IN
       IF count = 0 THEN
         /\ cand' = v
         /\ count' = 1
       ELSE IF v = cand THEN
         /\ count' = count + 1
         /\ UNCHANGED cand
       ELSE
         /\ count' = count - 1
         /\ UNCHANGED cand
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec ==
  /\ Init
  /\ [][Scan]_vars
  /\ WF_vars(Scan)

Correct ==
  /\ pos = Len(seq) + 1
  /\ \A v \in Values : (2 * Cardinality({i \in 1 .. Len(seq) : seq[i] = v}) > Len(seq)) => v = cand

Inv == \A v \in Values : (2 * Cardinality({i \in 1 .. Len(seq) : seq[i] = v}) > Len(seq)) => v = cand

Progress == \E v \in Values : 2 * Cardinality({i \in 1 .. Len(seq) : seq[i] = v}) > Len(seq)

====
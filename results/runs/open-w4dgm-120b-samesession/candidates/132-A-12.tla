---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

BoundedSeq(n) == IF n = 0 THEN {}
                 ELSE [i \in 1..n |-> CHOOSE x \in Values : TRUE]

TypeOK ==
  /\ seq \in BoundedSeq(bound)
  /\ pos \in 1..(Len(seq) + 1)
  /\ cand \in Values
  /\ count \in 0..bound

Init ==
  /\ seq \in BoundedSeq(bound)
  /\ pos = 1
  /\ cand \in Values
  /\ count = 0

Scan ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF count = 0 THEN /\ cand' = x /\ count' = 1
       ELSE IF x = cand THEN count' = count + 1 /\ cand' = cand
       ELSE count' = count - 1 /\ cand' = cand
  /\ pos' = pos + 1
  /\ seq' = seq

Next == Scan

Spec == Init /\ [][Next]_vars

PartTrue(v) == Cardinality({i \in 1..Len(seq) : seq[i] = v}) * 2 > Len(seq)

Correct == (\E v \in Values : PartTrue(v)) => (pos = Len(seq) + 1 => cand = CHOOSE v \in Values : PartTrue(v))

Inv == pos >= 1 /\ count >= 0

Spec == Init /\ [][Next]_vars
====
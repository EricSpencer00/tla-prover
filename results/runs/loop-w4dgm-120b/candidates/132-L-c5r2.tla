---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

BoundedSeq == [n \in 0..bound |-> [1..n -> Values]]

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1..(Len(seq) + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

TrueMajority ==
  \E v \in Values :
    /\ 2 * Cardinality({k \in 1..Len(seq) : seq[k] = v}) > Len(seq)
    /\ v = cand

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Scan ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       /\ cand' = IF cnt = 0 THEN x ELSE cand
       /\ cnt' = IF cnt = 0 THEN 1
                 ELSE IF cand = x THEN cnt + 1 ELSE cnt - 1
  /\ pos' = pos + 1
  /\ seq' = seq

Next == Scan

Spec == Init /\ [][Next]_vars /\ WF_vars(Scan)

Inv == cnt >= 0

Properties == Spec /\ Inv

====
---- MODULE MCMajority ----
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

Elems == {A, B, C}
Seqs == UNION {[1..n -> Elems] : n \in 0..bound}
SeqLen(s) == IF s = <<>> THEN 0 ELSE Len(s)

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 1..(bound + 1)
  /\ cand \in Elems
  /\ cnt \in 0..bound

Init ==
  /\ seq \in Seqs
  /\ pos = 1
  /\ cand \in Elems
  /\ cnt = 0

Scan ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN cand' = x /\ cnt' = 1
       ELSE IF cand = x THEN cnt' = cnt + 1 /\ cand' = cand
       ELSE cnt' = cnt - 1 /\ cand' = cand
  /\ pos' = pos + 1

Next == Scan

Spec == Init /\ [][Next]_vars

Correct ==
  \A x \in Elems : (2 * Cardinality({i \in DOMAIN seq : seq[i] = x}) > SeqLen(seq))
                     => (cand = x)

Inv ==
  \A i \in DOMAIN seq : seq[i] \in Elems

ScanCompletes == pos > Len(seq)

Properties == [p \in {ScanCompletes} |-> TRUE]

====
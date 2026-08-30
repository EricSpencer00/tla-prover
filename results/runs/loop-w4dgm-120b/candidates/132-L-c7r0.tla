---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

TypeOK ==
  /\ bound \in Nat
  /\ \A x \in (BoundedSeq({A, B, C}, bound}) : x \in {A, B, C}
  /\ pos \in 0..bound
  /\ candidate \in {A, B, C}
  /\ cnt \in Nat

Spec == Init /\ [][Next]_vars

vars == <<seq, pos, candidate, cnt>>
nodes == {A, B, C}

BoundedSeq(E, n) == UNION { [1..k -> E] : k \in 0..n }

Init ==
  /\ seq \in BoundedSeq(nodes, bound)
  /\ pos = 1
  /\ candidate \in nodes
  /\ cnt = 0

Next ==
  /\ IF pos <= Len(seq) THEN
       LET cur == seq[pos] IN
         /\ IF cnt = 0 THEN /\ candidate' = cur /\ cnt' = 1
            ELSE IF cur = candidate THEN cnt' = cnt + 1 / candidate' = candidate
            ELSE cnt' = cnt - 1 /\ candidate' = candidate
         /\ pos' = pos + 1
         /\ seq' = seq
     ELSE UNCHANGED <<seq, pos, candidate, cnt>>

Correct ==
  \A x \in nodes : (2 * Cardinality({i \in DOMAIN seq : seq[i] = x}) > Len(seq)) => x = candidate

Inv ==
  /\ cnt \in 0..bound
  /\ candidate \in nodes
  /\ pos \in 0..bound
  /\ seq \in BoundedSeq(nodes, bound)

====
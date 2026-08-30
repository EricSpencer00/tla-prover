---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, counter

vars == <<seq, pos, cand, counter>>

TypeOK ==
  /\ seq \in [1..bound -> Values]
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ counter \in 0..bound

Init ==
  /\ seq \in [1..bound -> Values]
  /\ pos = 1
  /\ cand \in Values
  /\ counter = 0

Next ==
  \/ IF pos <= bound
       THEN /\ LET v == seq[pos] IN
              /\ IF counter = 0
                   THEN cand' = v
                   ELSE IF v = cand
                        THEN cand' = cand
                        ELSE cand' = cand
              /\ counter' = IF counter = 0 THEN 1
                             ELSE IF v = cand THEN counter + 1
                             ELSE counter - 1
            /\ pos' = pos + 1
       ELSE UNCHANGED vars
  /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars

Correct ==
  (pos = bound + 1 /\ \A c \in Values : (2 * Cardinality({i \in 1..bound : seq[i] = c}) > bound) => (cand = c))

Inv ==
  /\ counter >= 0
  /\ counter <= bound
  /\ (pos = 1 => (counter = 0 /\ \E x \in Values : cand = x))
  /\ (pos > 1 => counter >= 1)

BoundedSeq == [n \in Nat |-> [1..n -> Values]]

SeqBounded ==
  /\ seq \in BoundedSeq[bound]
  /\ seq # <<>>

====
---- MODULE MCMajority ----
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

Seed == 1

VARIABLES seq, pos, cand, cnt
vars == <<seq, pos, cand, cnt>>

BoundedSeq(S) == {f \in [1..n -> S] : n \in 0..bound}

TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Scan ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN /\ cand' = x
                     /\ cnt' = 1
       ELSE IF cand = x THEN cnt' = cnt + 1
                          /\ UNCHANGED cand
       ELSE cnt' = cnt - 1
            /\ UNCHANGED cand
  /\ pos' = pos + 1

Next == Scan

Spec == Init /\ [][Next]_vars /\ WF_vars(Scan)

Correct ==
  \A e \in Values :
     (2 * Cardinality({k \in 1..Len(seq) : seq[k] = e}) > Len(seq))
       => (pos > Len(seq) => cand = e)

Inv ==
  (pos > Len(seq) /\ cnt > 0) => (2 * Cardinality({k \in 1..Len(seq) : seq[k] = cand}) > Len(seq))

Complete == pos > Len(seq)

====
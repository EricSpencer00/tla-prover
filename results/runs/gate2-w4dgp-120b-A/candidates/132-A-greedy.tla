---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

BoundedSeq(S, n) == {f \in [1..m -> S] : m \in 0..n}

TypeOK ==
  /\ seq \in BoundedSeq(Values, bound)
  /\ pos \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

Init ==
  /\ seq \in BoundedSeq(Values, bound)
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Scan ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN /\ cand' = x /\ cnt' = 1
       ELSE IF cand = x THEN /\ cnt' = cnt + 1
       ELSE /\ cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Scan

Spec == Init /\ [][Next]_vars

Correct ==
  \A x \in Values :
    (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) => (cand = x)

Inv ==
  \A x \in Values :
    (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) => (cand = x)

Complete == pos > Len(seq)

SpecFair == Spec /\ WF_vars(Scan)

====
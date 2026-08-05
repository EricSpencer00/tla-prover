---- MODULE MCMajority ----
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

ASSUME bound \in Nat

SeqOf(n, S) == IF n = 0 THEN <<>> ELSE <<S[n]>> \o SeqOf(n - 1, S)
BoundedSeq == {SeqOf(n, S) : n \in 0..bound, S \in [1..bound -> Values]}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

ScanNext ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       /\ IF cnt = 0 THEN cand' = x /\ cnt' = 1
          ELSE IF x = cand THEN cnt' = cnt + 1
          ELSE cnt' > 0 /\ cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == ScanNext

Spec == Init /\ [][Next]_vars

Correct ==
  (\A x \in Values : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) => (x = cand))
  /\ (cnt = 0 => cand \notin Values)

Inv ==
  (\A a, b \in Values : (a # b /\ a \in Values /\ b \in Values) => Cardinality({i \in 1..Len(seq) : seq[i] = a}) = Cardinality({i \in 1..Len(seq) : seq[i] = b}))
  /\ ((cnt = 0 \/ \E x \in Values : cand = x) => (cnt \in Nat /\ \A x \in Values : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) => x = cand))

Complete == (\A i \in 1..bound : TRUE) ~> (pos > Len(seq))

====
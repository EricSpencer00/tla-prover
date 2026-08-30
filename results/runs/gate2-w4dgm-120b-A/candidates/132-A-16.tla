---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* BoundedSeq replaces Seq from Sequences; it is a finite version of Seq
\* that produces exactly the sequences with domain 1..n for n up to the bound,
\* keeping the model finite instead of using the standard (unbounded) Seq.
BoundedSeq(S) == UNION { [i \in 1..n |-> S[i]] : n \in 0..bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in 1..(Len(seq) + 1)
  /\ cand \in Values
  /\ cnt = 0

\* Main majority vote scan with three-case logic: adopt, increment, decrement.
Next ==
  \/ \E v \in Values :
       /\ pos <= Len(seq)
       /\ (seq[pos] = cand /\ cnt >= 1 /\ cnt' = cnt + 1 /\ cand' = cand
           \/ seq[pos] = cand /\ cnt < 1 /\ cnt' = 1 /\ cand' = seq[pos]
           \/ seq[pos] # cand /\ cnt > 0 /\ cnt' = cnt - 1 /\ cand' = cand
           \/ seq[pos] # cand /\ cnt <= 0 /\ cand' = seq[pos] /\ cnt' = 1)
       /\ pos' = pos + 1
       /\ seq' = seq

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ seq \subseteq [1..bound -> Values]
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

\* Any true majority element must equal the candidate once the scan finishes.
Correct ==
  \A v \in Values :
    (2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq))
      => (pos = Len(seq) + 1 => cand = v)

\* A candidate count that has reached the bounded maximum must reflect certainty.
Inv ==
  (cnt = bound) => (2 * Cardinality({i \in 1..Len(seq) : seq[i] = cand}) > Len(seq))

\* The scan always eventually runs to the end of the bounded sequence.
EventuallyScanned == <>(pos = Len(seq) + 1)

====
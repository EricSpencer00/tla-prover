---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

\* A bounded version of Seq: only functions from a contiguous index range
\* whose length is at most the configured bound over the model values.
BoundedSeq == {s \in [1..n -> Values] : n \in 0..bound}

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1..(Len(seq) + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

\* Advance one step of the Boyer-Moore scan over the input sequence.
Step ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN
         /\ cand' = x
         /\ cnt' = 1
       ELSE IF x = cand THEN
         /\ cnt' = cnt + 1
       ELSE
         /\ cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Step

\* The majority vote invariant: any true majority over the entire sequence
\* must coincide with the candidate element once the scan has finished.
Correct ==
  IF pos = Len(seq) + 1 THEN
    (cnt > 0) => (Cardinality({i \in 1..Len(seq) : seq[i] = cand}) > Len(seq) \div 2)
  ELSE TRUE

Inv == TypeOK /\ Correct

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* The .cfg overrides Seq with a bounded version, so the name on the right
\* must be defined here and the name on the left must not be.
BoundedSeq == {s \in [1..n -> Values] : n \in 0..bound}
====
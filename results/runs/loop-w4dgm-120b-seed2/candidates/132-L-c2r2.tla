---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* A finite version of Seq that a model-checking configuration can explore.
BoundedSeq == [n \in 0..bound |-> [i \in 1..n |-> CHOOSE v \in {A, B, C} : TRUE]]

VARIABLES seq, pos, cand, cnt

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in Nat
  /\ cand \in {A, B, C}
  /\ cnt \in Nat

\* An element that truly is the majority of the whole sequence must become
\* the candidate after scanning the entire sequence.
Correct ==
  \A e \in {A, B, C} : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = e}) > Len(seq))
                        => (pos = Len(seq) + 1 => cand = e)

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in {A, B, C}
  /\ cnt = 0

\* Boyer-Moore: three-way update of candidate and counter per element.
Step ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN /\ cand' = x
                     /\ cnt' = 1
       ELSE IF cand = x THEN /\ cnt' = cnt + 1
                          /\ cand' = cand
       ELSE /\ cnt' = cnt - 1
            /\ cand' = cand
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

Inv == TypeOK /\ Correct

\* A full scan of the bounded input is always eventually reached.
EventualPos == <>(pos = Len(seq) + 1)
====
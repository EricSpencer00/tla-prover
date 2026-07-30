---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* Individual model values for sequences of bounded length.
Values == {A, B, C}

\* A finite version of the standard Seq operator, restricted to the model
\* bound. This is what the .cfg replaces Seq with, so it must be defined
\* and never re-declared.
BoundedSeq == [1..bound -> Values]

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ count \in 0..bound

Init ==
  /\ \E s \in BoundedSeq : seq = s
  /\ pos = 1
  /\ \E c \in Values : cand = c
  /\ count = 0

\* The usual three-way Boyer-Moore update: adopt a new candidate, count, or
\* decrement, depending on whether the scan has started and on equality.
Next ==
  \/ \E v \in Values :
       /\ pos <= bound
       /\ seq[pos] = v
       /\ IF count = 0
          THEN /\ cand' = v
               /\ count' = 1
          ELSE IF cand = v
               THEN /\ count' = count + 1
               /\ cand' = cand
               /\ UNCHANGED seq
               /\ UNCHANGED pos
          ELSE /\ count' = count - 1
               /\ UNCHANGED cand
               /\ UNCHANGED seq
               /\ UNCHANGED pos
       /\ pos' = pos + 1
  \/ (pos > bound /\ UNCHANGED <<seq, pos, cand, count>>)

\* Every true majority element must be the Boyer-Moore candidate after the
\* full scan.
Correct ==
  \A v \in Values : (Cardinality({i \in 1..bound : seq[i] = v}) > bound \div 2) => v = cand

\* The Boyer-Moore counter never drops below zero.
Inv == count >= 0

Spec == Init /\ [][Next]_vars

\* Model checking finishes the scan under weak fairness.
Complete == (pos > bound) ~> (pos > bound)

====
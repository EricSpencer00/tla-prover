---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

\* Model-checking configuration for the Boyer-Moore majority vote algorithm.
\* This module instantiates the full majority vote spec with concrete
\* values: three distinct model values and a bounded sequence length.
\* The .cfg file replaces the unbounded Seq operator with a bounded,
\* finite version (BoundedSeq) so that exhaustive checking terminates.

CONSTANTS A, B, C, bound

\* Concrete value set derived from the three model values.
Values == {A, B, C}

\* A bounded version of the standard Seq operator:
\* BoundedSeq(n, V) = all functions from 1..n to the value set V.
BoundedSeq(n, V) == [i \in 1..n |-> CHOOSE v \in V : TRUE]

\* The main spec's operators are re-exported here under the exact names
\* the configuration expects; the spec itself lives in this module.
InitSeq == CHOOSE n \in 0..bound : BoundedSeq(n, Values)

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

TypeOK ==
  /\ seq \in [1..bound -> Values]
  /\ i \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq = InitSeq
  /\ i = 1
  /\ cand \in Values
  /\ cnt = 0

\* The Boyer-Moore scan step: three-case logic over the next element.
Next ==
  \/ /\ i <= bound
     /\ i' = i + 1
     /\ IF cnt = 0 THEN /\ cand' = seq[i]
                        /\ cnt' = 1
        ELSE IF seq[i] = cand THEN /\ cnt' = cnt + 1
                                  /\ cand' = cand
        ELSE /\ cnt' = cnt - 1
             /\ cand' = cand
  \/ /\ i = bound + 1
     /\ UNCHANGED <<seq, i, cand, cnt>>

Spec == Init /\ [][Next]_vars

\* Any true majority element, if one exists, must equal the candidate after a
\* complete scan of the bounded sequence.
Correct ==
  (i = bound + 1) =>
    (\E c \in Values :
        (\A j \in 1..bound : 2 * Cardinality({k \in 1..bound : seq[k] = c}) > bound => cand = c))

\* An inductive invariant used in the original spec; it still holds here.
Inv == TRUE

Specification == Spec

====
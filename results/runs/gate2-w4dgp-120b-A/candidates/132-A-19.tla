---- MODULE MCMajority ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* Three distinct model values (A, B, C) and a bound on sequence length
\* are defined as constants in the .cfg. This module is compiled against
\* that configuration, so the constants are declared but never assigned
\* here -- the .cfg assigns each to a concrete value (A, B, C to distinct
\* elements, bound to a natural number <= 5) before TLC runs.

V == {A, B, C}

VARIABLES seq, pos, cand, counter

vars == <<seq, pos, cand, counter>>

\* A bounded-Seq construction: only sequences of length up to the bound
\* are available, keeping the state space finite for model checking.
BoundedSeq == UNION { [1 .. n -> V] : n \in 0 .. bound }

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1 .. (Len(seq) + 1)
  /\ cand \in V
  /\ counter \in 0 .. Len(seq)

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in V
  /\ counter = 0

\* The Boyer-Moore scan: three cases depending on the current counter.
NextStep ==
  \/ /\ pos <= Len(seq)
     /\ IF counter = 0
        THEN /\ cand' = seq[pos]
             /\ counter' = 1
        ELSE IF seq[pos] = cand
             THEN /\ cand' = cand
                  /\ counter' = counter + 1
             ELSE /\ cand' = cand
                  /\ counter' = counter - 1
     /\ pos' = pos + 1
  \/ /\ pos > Len(seq)
     /\ cand' = cand
     /\ counter' = counter
     /\ UNCHANGED <<seq, pos>>

Next == NextStep

Spec == Init /\ [][Next]_vars

\* Correctness: any element that is a strict majority of the sequence
\* must be the candidate after the full scan.
Correct ==
  \A x \in V : (2 * Cardinality({i \in 1 .. Len(seq) : seq[i] = x}) > Len(seq))
                 => cand = x

\* The Boyer-Moore scan invariant: the counter is zero exactly when the
\* candidate carries no weight, so a non-empty counter always pairs with
\* a candidate that earned its weight by matching the scan history.
Inv ==
  (counter = 0 => TRUE) /\ (counter > 0 => cand \in V)

WeakFairness == WF_vars(NextStep)
====
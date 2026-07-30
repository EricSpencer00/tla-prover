---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound, Seq

\* All possible elements in this model.
Vals == {A, B, C}

\* The bounded set of sequences: the empty sequence and every sequence of
\* length up to the configured bound over the three model values.
Sequences ==
  {<<>>} \cup
    { [i \in 1..n |-> e[i]] : \E n \in 0..bound, e \in [1..n -> Vals] }

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

\* Inherit the three-case scan logic of the Boyer-Moore majority vote.
Next(state, x) ==
  /\ pos' = pos + 1
  /\ IF cand = 0 /\ count = 0
       THEN cand' = x /\ count' = 1
     ELSE IF cand = x
       THEN count' = count + 1
     ELSE count' = count - 1
  /\ UNCHANGED seq

\* The init operator is also inherited from the main spec: the empty sequence,
\* a fresh scan position, a nondetermined candidate, and a zero counter.
Init ==
  /\ seq = <<>>
  /\ pos = 1
  /\ \E x \in Vals : cand = x
  /\ count = 0

Next_ ==
  \E x \in Vals : Next(state, x)

Spec == Init /\ [][Next_]_vars

\* Every element of the current sequence lies in the three-element value set.
TypeOK ==
  /\ seq \in Sequences
  /\ pos \in Nat
  /\ cand \in Vals \cup {0}
  /\ count \in Nat

\* Main correctness: a true majority element must be the current scan
\* candidate once the scan has completed.
Correct ==
  (pos > Len(seq) /\ \E x \in Vals : 2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq) => cand = x)

\* The inductive invariant of the majority vote scan.
Inv == count >= 0

====
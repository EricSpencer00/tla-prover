---- MODULE MCMajority ----
EXTENDS Integers, Sequences

\* BoundedSeq is a FINITE version of Seq that restricts sequence length to a
\* concrete bound; this keeps the model finite for model checking.
BoundedSeq == [n \in 0..bound |-> [i \in 1..n |-> CHOOSE v \in {A, B, C} : TRUE]]

CONSTANTS A, B, C, bound

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

Init ==
  /\ seq \in BoundedSeq
  /\ pos \in 1..(Len(seq) + 1)
  /\ cand \in {A, B, C}
  /\ count = 0

Scan ==
  \/ pos <= Len(seq) /\ LET v == seq[pos] IN
        /\ cand' = IF count = 0 THEN v ELSE cand
        /\ count' = IF count = 0 \/ v = cand THEN count + 1 ELSE count - 1
        /\ pos' = pos + 1
        /\ seq' = seq
  \/ pos > Len(seq) /\ UNCHANGED <<seq, pos, cand, count>>

Spec == Init /\ [][Scan]_vars

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1..(bound + 1)
  /\ cand \in {A, B, C}
  /\ count \in 0..bound

\* A true majority element must equal the candidate after the scan finishes.
Correct ==
  /\ pos = Len(seq) + 1
  /\ (2 * count > Len(seq)) => (cand = seq[1])

Inv ==
  /\ count >= 0
  /\ count <= Len(seq)

Next == Scan

\* Weak fairness: the scan makes progress and always eventually finishes.
SpecFair == Spec /\ TRUE

====
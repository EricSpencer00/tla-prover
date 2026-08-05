---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

\* Boyer-Moore majority vote model-checking configuration.  The model
\* uses a bounded, finite version of Seq (BoundedSeq) so the state space
\* stays finite.  The three values A, B, C are the distinct elements
\* sequences are drawn from; 'bound' caps the maximum length checked.
CONSTANTS A, B, C, bound

VALUES == {A, B, C}

BoundedSeq(n, S) == {s \in Seq(S) : Len(s) = n}

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
  /\ seq \in BoundedSeq(0, VALUES) \cup BoundedSeq(1, VALUES) \cup BoundedSeq(2, VALUES)
                       \cup BoundedSeq(3, VALUES) \cup BoundedSeq(4, VALUES) \cup BoundedSeq(5, VALUES)
  /\ pos \in Nat
  /\ cand \in VALUES
  /\ count \in Nat

Init ==
  /\ \E n \in 0..bound : seq \in BoundedSeq(n, VALUES)
  /\ pos = 1
  /\ cand \in VALUES
  /\ count = 0

\* Boyer-Moore scan step: three cases on the current head element.
Step(e) ==
  /\ pos <= Len(seq)
  /\ \/ \A i \in 1..Len(seq) : seq' = [i \in 1..Len(seq) |-> IF i = pos THEN e ELSE seq[i]]
     /\ pos' = pos + 1
     /\ cand' = e
     /\ count' = 1
     \/ IF seq[pos] = cand
        THEN /\ cand' = cand
             /\ count' = count + 1
        ELSE /\ count = 0
             /\ cand' = seq[pos]
             /\ count' = count + 1
        /\ pos' = pos + 1

Next == \E e \in VALUES : Step(e)

Spec == Init /\ [][Next]_vars /\ WF_vars(pos <= Len(seq))

Correct ==
  \A i \in 1..Len(seq) : (2 * Cardinality({j \in 1..Len(seq) : seq[j] = seq[i]}) > Len(seq)) => cand = seq[i]

Inv ==
  \A i \in 1..Len(seq) : (2 * Cardinality({j \in 1..Len(seq) : seq[j] = seq[i]}) > Len(seq)) => cand = seq[i]

Complete == pos > Len(seq)

Theorem == Spec => []Complete

====
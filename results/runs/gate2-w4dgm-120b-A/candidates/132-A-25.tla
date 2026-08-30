---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}
AllSeqs == UNION { [1 .. n -> Values] : n \in 0 .. bound }

\* A bounded sequence constructor that mirrors Seq but stays finite for model checking.
BoundedSeq(S) == S

VARIABLES seq, i, cand, count

vars == <<seq, i, cand, count>>

TypeOK ==
  /\ seq \in AllSeqs
  /\ i \in 0 .. bound
  /\ cand \in Values
  /\ count \in 0 .. bound

Spec == Init /\ [][Next]_vars

Init ==
  /\ seq \in AllSeqs
  /\ i = 1
  /\ cand \in Values
  /\ count = 0

Next ==
  \/ \E e \in Values :
       /\ i <= Len(seq)
       /\ \/ (i <= Len(seq) /\ seq[i] = e /\ count' = count + 1)
          \/ (i <= Len(seq) /\ seq[i] # e /\ count > 0 /\ count' = count - 1)
          \/ (count = 0 /\ cand' = e)
       /\ i' = i + 1
       /\ UNCHANGED seq
  \/ \E s \in AllSeqs :
       /\ seq' = s
       /\ i' = 1
       /\ UNCHANGED <<cand, count>>

Correct ==
  /\ (i > Len(seq) /\ count > 0)
     => \A j \in 1 .. Len(seq) : seq[j] = cand

Inv == \A v \in Values : Cardinality({j \in 1 .. Len(seq) : seq[j] = v}) <= bound

BoundedSeq == BoundedSeq
Spec == Spec
TypeOK == TypeOK
Correct == Correct
Inv == Inv
====
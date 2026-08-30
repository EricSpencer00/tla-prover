---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* Value domain: the three model values, taken from the description.
Values == {A, B, C}

\* The sequence domain: all functions from 1..n to Values for n <= bound.
SeqDomain == UNION { [1..n -> Values] : n \in 0..bound }

\* The model redefines Seq to a bounded version of the standard operator.
Seq == BoundedSeq

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
  /\ seq \in SeqDomain
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ count \in 0..bound

\* Scan head: the element at the next position, only defined while it exists.
Head == IF pos <= Len(seq) THEN seq[pos] ELSE A

Init ==
  /\ seq \in SeqDomain
  /\ pos = 1
  /\ cand \in Values
  /\ count = 0

\* The majority vote's three-way logic applied to the scan head.
Scan ==
  /\ pos <= Len(seq)
  /\ IF pos = 1 THEN
       /\ cand' = Head
       /\ count' = 1
     ELSE IF Head = cand THEN
       /\ cand' = cand
       /\ count' = count + 1
     ELSE IF count > 0 THEN
       /\ cand' = cand
       /\ count' = count - 1
     ELSE
       /\ cand' = Head
       /\ count' = 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Scan

Spec == Init /\ [][Next]_vars /\ WF_vars(Scan)

\* Any true majority element must equal the candidate after a complete scan.
Correct ==
  (pos = Len(seq) + 1 /\ count > 0) => (\A v \in Values : v # cand => Cardinality({k \in 1..Len(seq) : seq[k] = v}) * 2 <= Len(seq))

\* The candidate-counter representation is the well-known majority-indicator.
Inv == (count > 0) => (2 * Cardinality({k \in 1..Len(seq) : seq[k] = cand}) > Len(seq))

\* Type correctness of every variable and the main correctness relation.
TypeOK == TypeOK /\ Correct

Completion == pos = Len(seq) + 1

StateBound == pos <= Len(seq) + 1

====
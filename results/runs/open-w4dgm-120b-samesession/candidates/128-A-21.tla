---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, Functions

CONSTANTS Values, MaxSeqLen

Sqrt(n) == IF n = 0 THEN 0 ELSE 1 + Sqrt(n - 1)

VARIABLES seq, origSeq, work, pc

vars == <<seq, origSeq, work, pc>>

Intervals == {i \in 1..MaxSeqLen : \E j \in 1..MaxSeqLen : i <= j}

SubSeq(sq, i, j) == [k \in i..j |-> sq[k]]

RECURSIVE SumOver(_)
SumOver(S) == IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE IN sq[x] + SumOver(S \ {x})

\* A partition keeps elements outside the interval unchanged and forces
\* elements at or below the pivot index to be no greater than those above.
Permutations(sq, i, j, p) ==
  /\ p[pivot] = sq[pivot]
  /\ \A k \in 1..MaxSeqLen : ~(i <= k /\ k <= j) => p[k] = sq[k]
  /\ \A a \in i..p \in i..j : a <= p => p[a] <= p[p]

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ origSeq \in [1..MaxSeqLen -> Values]
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "terminated"}

Init ==
  /\ \E s \in [1..MaxSeqLen -> Values] :
        /\ \A i \in 1..MaxSeqLen : s[i] \in Values
        /\ seq = s
        /\ origSeq = s
  /\ work = {1..MaxSeqLen}
  /\ pc = "loop"

RelativelySorted ==
  /\ \A i \in 1..MaxSeqLen : seq[i] \in Values
  /\ \A i, j \in 1..MaxSeqLen : i < j => seq[i] <= seq[j]
  /\ \A i, j \in 1..MaxSeqLen : (i, j) \in work => seq[i] <= seq[j]

\* A partition is a permutation on the whole domain, chosen nondeterministically.
DomainPartitions ==
  /\ \E perm \in [1..MaxSeqLen -> 1..MaxSeqLen] :
        /\ \A i \in 1..MaxSeqLen : perm[i] \in 1..MaxSeqLen
        /\ \A i, j \in 1..MaxSeqLen : perm[i] = perm[j] => i = j
  /\ \A i, j \in 1..MaxSeqLen : (i, j) \in work => seq[i] <= seq[j]

Inv == RelativelySorted /\ DomainPartitions

PCorrect == (pc = "terminated") => (seq = origSeq /\ RelativelySorted)

Step ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E I \in work :
        /\ Cardinality(I) = 1
        /\ work' = work \ {I}
        /\ pc' = IF work \ {I} = {} THEN "terminated" ELSE pc
        /\ UNCHANGED <<seq, origSeq>>
  /\ \E I \in work, pivot \in I :
        /\ Cardinality(I) > 1
        /\ \E lo \in {i \in I : i < pivot} \cup {I} :
             hi = {i \in I : i > pivot}
        /\ \E newSeq \in Permutations(seq, \A i \in I : i, pivot) :
             seq' = newSeq
        /\ work' = (work \ {I}) \cup lo \cup hi
        /\ pc' = IF (work \ {I}) \cup lo \cup hi = {} THEN "terminated" ELSE pc
        /\ UNCHANGED origSeq

Stall ==
  /\ pc = "terminated"
  /\ UNCHANGED vars

Next == Step \/ Stall

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Step)

\* Weak fairness on the transition out of the loop forces eventual termination.
Termination == pc = "terminated"

LimitedSeq(n) == IF n <= MaxSeqLen THEN n ELSE MaxSeqLen
====
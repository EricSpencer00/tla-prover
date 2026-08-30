---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* The spec is a Quicksort analogue: partitioning is abstracted into an
\* uninterpreted choice over any valid partition of the interval.
\* Invariance is a nested-permutation+sortedness shape; termination is
\* guaranteed by weak fairness on the work-set shrinking.

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

VARIABLES seq, origSeq, work, pc

vars == <<seq, origSeq, work, pc>>

\* Permutations of a domain as the range of an automorphism of that domain.
Domain == 1..Len(seq)
Permutation == {f \in [Domain -> Domain] : \A x, y \in Domain : f[x] = f[y] => x = y}

RECURSIVE BoundedSeq(_, _)
BoundedSeq(f, n) == IF n = 0 THEN <<>> ELSE <<f[n]>> \o BoundedSeq(f, n - 1)

TypeOK ==
  /\ seq \in Seq(Values)
  /\ origSeq \in Seq(Values)
  /\ Len(seq) <= MaxSeqLen
  /\ work \subseteq Intervals
  /\ pc \in {"main", "done"}

Init ==
  /\ \E s \in Seq(Values) : Len(s) >= 1 /\ Len(s) <= MaxSeqLen /\ seq = s
  /\ origSeq = seq
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "main"

Narrow(i) == i.lo = i.hi

\* The uninterpreted partition operator: the set of all reordered sequences
\* that respect the pivot split and leave the rest untouched.
PARTITION(i, p) ==
  {BoundedSeq(j, Len(seq)) : \E j \in Permutation :
     /\ \A k \in 1..Len(seq) : (k < i.lo \/ k > i.hi) => j[k] = k
     /\ \A k \in i.lo..i.hi : k <= p => seq[k] <= seq[j[p + 1]]
     /\ \A k \in i.lo..i.hi : k > p => seq[j[p + 1]] <= seq[k]}
StateDown(i) == [lo |-> i.lo, hi |-> i.hi]
StateUp(i) == [lo |-> i.lo, hi |-> i.hi]

Step ==
  /\ pc = "main"
  /\ work # {}
  /\ \E i \in work :
       /\ work' = work \ {i}
       /\ IF Narrow(i)
          THEN work'
          ELSE \/ \E p \in i.lo..i.hi :
                 /\ \E pseq \in PARTITION(i, p) : seq' = pseq
                 /\ work' = work \cup {StateDown(i), StateUp([lo |-> p + 1, hi |-> i.hi])}
                 \/ UNCHANGED <<seq, origSeq, pc>>
  /\ UNCHANGED origSeq

Done ==
  /\ pc = "main"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, origSeq, work>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next_ == Step \/ Done \/ Stall

Spec == Init /\ [][Next_]_vars /\ WF_vars(Step)

\* A partitioned interval stays "sorted": everything on its left stays below
\* everything on its right, so interval-wise sortedness is preserved before
\* the interval is even split into singletons.
PCorrect ==
  /\ (work = {} => \A x \in 1..Len(seq), y \in 1..Len(seq) : x < y => seq[x] <= seq[y])
  /\ (work # {} => \A i \in work : \A x, y \in i.lo..i.hi : x < y => seq[x] <= seq[y])

PermutationPreserved ==
  /\ \A i \in Domain : seq[i] \in Values
  /\ \E e \in Permutation : \A i \in Domain : seq[i] = origSeq[e[i]]

RelativeSorted ==
  \A i \in Intervals :
    /\ i.lo \in Domain /\ i.hi \in Domain
    /\ (i.lo <= i.hi => \A x, y \in i.lo..i.hi : x < y => seq[x] <= seq[y])

Inv == PermutationPreserved /\ RelativeSorted

Termination == <>(pc = "done")

\* The bounded-length sequence operator is redefined here just for
\* model checking; the full Seq operator is still available via Sequences.
LimitedSeq(f) == BoundedSeq(f, MaxSeqLen)

====
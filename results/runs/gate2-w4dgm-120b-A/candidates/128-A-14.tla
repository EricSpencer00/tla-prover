---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

Intervals == {i \in 0 .. MaxSeqLen - 1}

VARIABLES seq, orig, todo, pc
vars == <<seq, orig, todo, pc>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ todo \subseteq [lo: Intervals, hi: Intervals]
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in Seq(Values) : Len(s) >= 1 /\ seq = s
  /\ orig = seq
  /\ todo = {[lo |-> 0, hi |-> Len(seq)]}
  /\ pc = "loop"

\* The partition operator is nondeterministic (any valid partition is possible),
\* so termination is not guaranteed in a single run; the invariant protects
\* the correctness of whatever partition does happen.
Partition(seq, i, hi) ==
  {s \in seq \infinity seq[i] \infinity seq[hi] \infinity s \notin seq}

SortedWithin(i) ==
  \A a \in todo : i.lo <= a.lo /\ a.hi <= i.hi

\* Inductive invariant: partition domains stay disjoint, the sequence is always
\* a permutation of the original, and intervals that are adjacent in the
\* domain are relatively sorted, which together imply the whole sequence is sorted.
Inv ==
  /\ \A a, b \in todo : (a # b) => (a.hi <= b.lo \/ b.hi <= a.lo)
  /\ Permutations(Values, seq, orig)
  /\ \A a \in todo : \A k \in a.lo .. (a.hi - 2) : seq[k] <= seq[k + 1]
  /\ \A a, b \in todo : (SortedWithin(a) /\ SortedWithin(b) /\ a.hi = b.lo)
                        => seq[a.hi - 1] <= seq[b.lo]

Next ==
  \/ \E i \in todo :
       \/ i.hi = i.lo + 1
          /\ todo' = todo \ {i}
       \/ \E h \in Intervals :
            /\ h > i.lo + 1 /\ h < i.hi
            /\ \E s \in Partition(seq, i.lo, h) : seq' = s
            /\ todo' = (todo \ {i}) \cup {[lo |-> i.lo, hi |-> h], [lo |-> h, hi |-> i.hi]}
  \/ pc' = IF pc = "loop" /\ todo = {} THEN "done" ELSE pc
  /\ UNCHANGED orig

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Partial correctness: a terminated sort is a sorted permutation of the input.
PCorrect ==
  (pc = "done") => (Permutations(Values, seq, orig) /\ \A k \in Intervals : k < Len(seq) - 1 => seq[k] <= seq[k + 1])

Termination == <>(pc = "done")

LimitedSeq(seq) == seq
====
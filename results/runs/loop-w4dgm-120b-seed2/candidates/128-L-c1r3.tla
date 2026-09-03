---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANT Values, MaxSeqLen

\* A finite, model-checkable version of Seq from the Sequences module.
LimitedSeq(f, n) == IF n = 0 THEN <<>> ELSE <<f[n]>> \o LimitedSeq(f, n - 1)

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
Slices(i, j) == {k \in 1..MaxSeqLen : i <= k /\ k <= j}
Domain == UNION {Slices(i.lo, i.hi) : i \in Intervals}

Half(i, a) == IF 2 * a <= i THEN 0 ELSE i

TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ work \subseteq Intervals
  /\ pc \in {"main", "halt"}

Init ==
  /\ \E s \in Seq(Values) : seq = s /\ orig = s
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "main"

\* One iteration: pick an interval, partition it around a pivot, and refine.
Step ==
  /\ pc = "main"
  /\ work # {}
  /\ \E i \in work :
       /\ work' = work \ {i}
       /\ IF i.lo = i.hi
          THEN work'
          ELSE
            /\ \E pivot \in i.lo..i.hi :
                 /\ \E ns \in { ns \in Seq(Values) :
                                   /\ Len(ns) = Len(seq)
                                   /\ \A k \in Domain :
                                        (k \in Slices(i.lo, pivot) /\ k \in Slices(pivot + 1, i.hi))
                                          => ns[k] = seq[k] /\ ns[pivot] = seq[pivot]
                                        \/ (k \in Slices(i.lo, pivot) => ns[k] <= seq[pivot])
                                        \/ (k \in Slices(pivot + 1, i.hi) => ns[pivot] <= ns[k])
                                   /\ \A k \in 1..Len(seq) : k \notin Slices(i.lo, i.hi) => ns[k] = seq[k]
                               }
                 /\ seq' = ns
                 /\ work' = work \cup {[lo |-> i.lo, hi |-> pivot], [lo |-> pivot + 1, hi |-> i.hi]}
       /\ pc' = IF work' = {} THEN "halt" ELSE pc
  /\ UNCHANGED orig

Halt ==
  /\ pc = "halt"
  /\ UNCHANGED vars

Stall == Halt \/ Step

Spec == Init /\ [][Step]_vars /\ WF_vars(Halt)

PermutationPreserved(p) == \A k \in Domain : p[k] = seq[k]

\* Relative sortedness: an interval always lies entirely to the left or right of
\* everything to its right, so the whole sequence is globally sorted.
RelativeSortedness ==
  \A a, b \in work :
    \/ (a.hi < b.lo /\ \A x \in Slices(a.lo, a.hi), y \in Slices(b.lo, b.hi) : seq[x] <= seq[y])
    \/ (b.hi < a.lo /\ \A x \in Slices(b.lo, b.hi), y \in Slices(a.lo, a.hi) : seq[x] <= seq[y])

PCorrect ==
  /\ work = {}
  /\ PermutationPreserved(orig)
  /\ RelativeSortedness

Termination == []<>(pc = "halt")

====
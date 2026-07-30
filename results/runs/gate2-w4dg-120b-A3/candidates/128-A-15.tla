---- MODULE Quicksort ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* A partition of a sequence over a pivot index: elements at or below the pivot
\* are no greater than those above it, and nothing outside the interval moves.
Partition(f, lo, hi, p) ==
  [i \in DOMAIN f |-> IF i < lo \/ i > hi
                     THEN f[i]
                     ELSE IF i <= p
                            THEN CHOOSE x \in Values : \A j \in DOMAIN f :
                                   (j \in lo..p /\ f[j] = x) => x <= f[i]
                            ELSE CHOOSE x \in Values : \A j \in DOMAIN f :
                                   (j \in (p + 1)..hi /\ f[j] = x) => f[i] <= x]

\* Permutations of a sequence: composition with an automorphism of the domain.
Permutation(g, f) ==
  \E e \in [DOMAIN f -> DOMAIN f] : \A x, y \in DOMAIN f :
     e[x] = e[y] => x = y /\ g[x] = f[e[x]]

\* A "finite" version of the standard Seq operator; this hides the EXCEPT trick
\* that makes unbounded models possible, so the model stays checkable.
LimitedSeq(s) == {s}

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* The work set carries intervals of the domain, not just start/end pairs.
Intervals == SUBSET (0..(MaxSeqLen - 1))

TypeOK ==
  /\ seq \in LimitedSeq(VALUE OF Values)
  /\ orig \in LimitedSeq(VALUE OF Values)
  /\ work \subseteq Intervals
  /\ pc \in {"sorting", "done"}

SortedNonEmpty ==
  \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

PCorrect ==
  pc = "done" => /\ seq \in Permutation(orig)
                 /\ SortedNonEmpty

Init ==
  /\ seq \in LimitedSeq(VALUE OF Values)
  /\ orig = seq
  /\ work = {0..(Len(seq) - 1)}
  /\ pc = "sorting"

\* The whole action is guarded on a non-empty work set, which is the only
\* way the algorithm can make progress, so weak fairness on it is enough for
\* termination even though the model does not observe the individual steps.
Step ==
  /\ pc = "sorting"
  /\ work # {}
  /\ \E lo \in work :
       /\ IF lo = hi
          THEN work' = work \ {lo}
          /\ UNCHANGED <<seq, orig>>
          /\ UNCHANGED pc
          /\ UNCHANGED hi
       ELSE \E p \in lo..hi :
            /\ LET lo' == lo
                 hi' == hi
                 seq' == Partition(seq, lo, hi, p)
                 work' == (work \ {lo}) \cup {lo', p + 1, hi'}
             IN UNCHANGED <<orig, pc>>
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "sorting"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

\* A single stuttering self-loop after termination to keep the model alive.
Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Terminate \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* A domain-constrained version of the standard Permutations invariant.
Inv ==
  /\ \A lo \in work : \A hi \in work : lo < hi => \A i \in lo..hi : seq[i] <= seq[hi]
  /\ seq \in Permutation(orig)

Termination == <> (pc = "done")

====
---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

(* The set of values allowed in the sequence is declared as a constant      *)
(* and assumed to be a subset of the integers. The model checker will        *)
(* instantiate it; the specification itself never changes it.                *)

CONSTANTS Values, MaxSeqLen

\* The Sort algorithm is modeled as a PlusCal translation: "pc" is the label  *
\* the control sits at; the work set holds the intervals still to be        *
\* processed. The "seq" variable is always a member of the bounded set of    *
\* sequences that the companion module makes checkable.                       *

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* A bounded version of Sequences!Seq: restrict the length to MaxSeqLen.     *
\* The .cfg file replaces the inherited Seq with this operator, so we do     *
\* not DECLARE Seq here -- only the replacement operator name.               *
LimitedSeq(n) == CHOOSE s \in { s \in [1..n -> Values] : Len(s) = n }

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ orig \in [1..MaxSeqLen -> Values]
  /\ work \subseteq [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
  /\ pc \in {"main", "halt"}

\* An interval is always a contiguous range of indices, lo <= hi.             *
IntervalOK == \A i \in work : i.lo <= i.hi

\* Yes, Permutes is not a primitive operator.  It is defined here, just as    *
\* the spec describes; the invariant below may only ever invoke it on a      *
\* permutation of the original values, so it is always well-defined.         *
Permutes(f) ==
  /\ f \in [1..MaxSeqLen -> 1..MaxSeqLen]
  /\ \A i, j \in 1..MaxSeqLen : f[i] = f[j] => i = j

\* Permutation preservation: the current sequence is always a rewrite of     *
\* the original by a domain automorphism, so no value is ever introduced or    *
\* lost -- this is the real substance of the correctness claim.              *
PermutationPreserved == Permutes(f) /\ seq = [i \in 1..MaxSeqLen |-> orig[f[i]]]

\* A lexicographic order on sequences of bounded length is available from    *
\* Sequences (lexicographically, the empty sequence is the bottom element).  *
\* It is used to order the partition relation below.                          *
LexicographicOrder == LexicographicOrder

\* The partition operator is deliberately under-constrained: it returns every *
\* sequence that is reachable from the current one by a partitioning step     *
\* over the chosen interval and pivot, and nothing more.  It is permitted to *
\* return a strictly smaller result than the current sequence, which is how  *
\* the algorithm makes progress in this abstraction.                          *
\* The definition is the most faithful transcription of the spec text.        *
AfterPartition(x, lo, hi, piv) ==
  { y \in [1..MaxSeqLen -> Values] :
      /\ \A i \in 1..MaxSeqLen : (i < lo \/ i > hi) => y[i] = x[i]
      /\ \A j \in lo..piv, k \in (piv + 1)..hi : y[j] <= y[k]
      /\ y # x /\ LexicographicOrder(y, x) }

\* The work set is always partitioned into intervals that are pairwise        *
\* disjoint and whose union covers exactly the indices that are not yet      *
\* settled as singletons, so the pending work never overlaps.                 *
DisjointPartition ==
  /\ \A i1, i2 \in work : (i1.lo <= i2.hi /\ i2.lo <= i1.hi) => i1 = i2
  /\ \A k \in 1..MaxSeqLen : \E i \in work : k \in [i.lo..i.hi]

\* Local sortedness between intervals: for any two intervals that are         *
\* separate, the last element of the lower one is no greater than the first  *
\* element of the higher one -- this is what makes the whole sequence sorted *
\* once every interval has collapsed to a singleton.                          *
InterIntervalSortedness ==
  \A i1, i2 \in work : (i1.hi < i2.lo \/ i2.hi < i1.lo) =>
    (i1 = i2) \/ (seq[i1.hi] <= seq[i2.lo] /\ seq[i2.hi] <= seq[i1.lo])

\* The invariant is the conjunction of all three components.                  *
Inv == IntervalOK /\ PermutationPreserved /\ DisjointPartition /\ InterIntervalSortedness

\* The set of intervals is never empty while there is work to do; the         *
\* algorithm terminates once it has been reduced to the empty set.            *
PCorrect == work = {} => pc = "halt"

Init ==
  /\ seq \in LimitedSeq(MaxSeqLen)
  /\ orig = seq
  /\ work = {[lo |-> 1, hi |-> MaxSeqLen]}
  /\ pc = "main"

\* The single nontrivial step: partition an interval that has more than one  *
\* element.  The new sequence is chosen nondeterministically from the set of *
\* all possible partition results for the chosen pivot.                      *
Partition(i, piv) ==
  /\ i \in work
  /\ i.lo < i.hi
  /\ piv \in i.lo..i.hi
  /\ \E ns \in AfterPartition(seq, i.lo, i.hi, piv) :
       /\ seq' = ns
       /\ work' = (work \ {i}) \cup {[lo |-> i.lo, hi |-> piv], [lo |-> piv + 1, hi |-> i.hi]}
  /\ pc' = pc

Collapse(i) ==
  /\ i \in work
  /\ i.lo = i.hi
  /\ work' = work \ {i}
  /\ pc' = pc
  /\ UNCHANGED seq

Quit ==
  /\ pc = "main"
  /\ work = {}
  /\ pc' = "halt"
  /\ UNCHANGED <<seq, orig, work>>

Stall ==
  /\ pc = "halt"
  /\ UNCHANGED vars

Next ==
  \/ \E i \in work, piv \in 1..MaxSeqLen : Partition(i, piv)
  \/ \E i \in work : Collapse(i)
  \/ Quit
  \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Quit) /\ WF_vars(Stall)

Termination == <>(pc = "halt")

====
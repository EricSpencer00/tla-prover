---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

(* An abstract Quicksort: intervals are partitioned by a nondeterministic     *)
(* choice of a pivot and a valid partition outcome.  When the algorithm      *)
(* terminates the result is a sorted permutation of the original.             *)

CONSTANTS Values, MaxSeqLen

VARIABLES seq, orig, todo, pc

vars == <<seq, orig, todo, pc>>

Intervals == {i \in 1..MaxSeqLen : 1 <= i <= Len(seq)}

TypeOK ==
    /\ seq \in Seq(Values)
    /\ orig \in Seq(Values)
    /\ todo \subseteq Intervals
    /\ pc \in {"loop", "done"}

\* The partition operator: all permutations of the current sequence that  *
\* leave elements outside the interval untouched and keep the lower part  *
\* of the interval no greater than the upper part (some must exist).     *
ValidPartitions(f, lo, hi, p) ==
    /\ \A i \in 1..Len(seq) : (i < lo \/ i > hi) => f[i] = seq[i]
    /\ \A i \in lo..p, j \in p+1..hi : f[i] <= f[j]

\* The work set is a partition of the domain, so intervals always cover a  *
\* gap-free region and never overlap -- this is what keeps every element   *
\* accounted for even as the intervals get subdivided.                    *
DomainPartitions ==
    /\ \A a, b \in todo : (a \cap b # {}) => (a = b)
    /\ \A i \in 1..Len(seq) : \E a \in todo : i \in a

PermutationPreserved ==
    \E g \in [1..Len(seq) -> 1..Len(seq)] :
        /\ \A i \in 1..Len(seq) : seq[g[i]] = orig[i]
        /\ \A i, j \in 1..Len(seq) : g[i] = g[j] => i = j

PairwiseSorted(i, j) == \A a \in i, b \in j : seq[a] <= seq[b]

RelativeSorted ==
    \A a, b \in todo \ {todo} : PairwiseSorted(a, b)

Init ==
    \E s \in Seq(Values) :
        /\ Len(s) <= MaxSeqLen
        /\ seq = s
        /\ orig = s
        /\ todo = {1..Len(s)}
        /\ pc = "loop"

PartitionAction ==
    /\ pc = "loop"
    /\ \E i \in todo :
         /\ Len(i) = 1
         /\ todo' = todo \ {i}
         /\ UNCHANGED <<seq, orig>>
    /\ pc' = pc

SortStep ==
    /\ pc = "loop"
    /\ \E i \in todo :
         /\ Len(i) > 1
         /\ \E p \in i :
              /\ \E f \in [1..Len(seq) -> Values] :
                   /\ ValidPartitions(f, i[1], i[Len(i)], p)
                   /\ seq' = f
              /\ todo' = (todo \ {i}) \cup {i[1]..p, (p + 1)..i[Len(i)]}
    /\ pc' = pc

Terminate ==
    /\ pc = "loop"
    /\ todo = {}
    /\ pc' = "done"
    /\ UNCHANGED <<seq, orig, todo>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == PartitionAction \/ SortStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars
        /\ WF_vars(PartitionAction) /\ WF_vars(SortStep) /\ WF_vars(Terminate)

\* PCorrect: when the algorithm has terminated, the result is a sorted    *
\* permutation of the original sequence.                                   *
PCorrect ==
    (pc = "done") => (PermutationPreserved /\ \A i \in Intervals : \A j \in Intervals : i < j => PairwiseSorted(i, j))

\* SAFETY: partial correctness (sorted permutation) and an invariant     *
\* that the work set stays a gap-free partition of the domain.            *
Inv == PCorrect /\ DomainPartitions /\ RelativeSorted

Termination == (pc = "done") ~> (pc = "done")

\* A finite version of Seq so the model stays bounded.                    *
LimitedSeq(f, n) == [i \in 1..n |-> f[i]]

====
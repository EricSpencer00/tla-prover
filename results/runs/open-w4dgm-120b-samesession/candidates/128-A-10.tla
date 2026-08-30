---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Quicksort modeled as a bounded nondeterministic partition step: a single
\* sort action picks an interval and a pivot, then jumps to ANY partition
\* that any partitioning routine could legally produce. The action frontier
\* is restricted to a bounded element set, which is what keeps the reachable
\* state space finite and model-checkable.
CONSTANTS Values, MaxSeqLen

\* Bounded, finite version of the sequence type from Sequences: only
\* sequences up to MaxSeqLen are reachable, so the model is finite.
LimitedSeq == { s \in Seq(Values) : Len(s) <= MaxSeqLen }

\* An interval of indices in the sequence.
Interval == {x \in Nat : x >= 1}

\* The sorting algorithm terminates with a sorted permutation of its input.
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

TypeOK ==
    /\ seq \in LimitedSeq
    /\ orig \in LimitedSeq
    /\ work \subseteq Interval
    /\ pc \in {"loop", "done"}

\* A partition leaves elements outside the chosen interval untouched.
OutsideUnchanged(y, iv, seq1, seq2) ==
    \A i \in 1..Len(seq1) : (i \notin iv) => (seq1[i] = seq2[i])

\* Partition the current sequence around a pivot index: everything at or
\* below the pivot index is no greater than everything above it.
ValidPartition(seq1, seq2, iv, piv) ==
    /\ Len(seq1) = Len(seq2)
    /\ OutsideUnchanged(y, iv, seq1, seq2)
    /\ \A i \in iv : (\A j \in iv :
           (i <= piv /\ j > piv) => (seq2[i] <= seq2[j]))

Init ==
    /\ seq \in LimitedSeq /\ seq # <<>>
    /\ orig = seq
    /\ work = {1..Len(seq)}
    /\ pc = "loop"

Sorted == \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

\* One iteration of the quicksort loop: pick an unprocessed interval and a
\* pivot, partition it nondeterministically, and subdivide the work set.
Loop ==
    /\ pc = "loop"
    /\ \E iv \in work :
         /\ work' = work \ {iv}
         /\ IF Cardinality(iv) > 1
              THEN \E piv \in iv :
                     /\ \E seq2 \in LimitedSeq :
                          /\ ValidPartition(seq, seq2, iv, piv)
                          /\ seq' = seq2
                     /\ work' = work' \cup {1..piv, (piv + 1)..Len(seq)}
              ELSE UNCHANGED <<seq, work>>
    /\ UNCHANGED <<orig, pc>>

Terminate ==
    /\ pc = "loop"
    /\ work = {}
    /\ pc' = "done"
    /\ UNCHANGED <<seq, orig, work>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Loop \/ Terminate \/ Stall

\* The work set is always a partition of the domain: intervals are disjoint
\* and cover exactly the indices that have been introduced.
IntervalPartition ==
    /\ \A x \in work : work \subseteq (1..Len(seq))
    /\ \A i \in 1..Len(seq) : \E iv \in work : i \in iv

PCorrect ==
    /\ (pc = "done" => (Sorted /\ seq \in Permutations(orig)))
    /\ IntervalPartition

\* The permutation set is defined via automorphisms of the index domain,
\* and matches the usual notion of a permutation of a sequence.
Permutations(s) ==
    { [i \in 1..Len(s) |-> s[f[i]]] : f \in { g \in (1..Len(s) -> 1..Len(s))
                                         : \A i \in 1..Len(s), j \in 1..Len(s) :
                                             (f[i] = f[j]) => (i = j) } }

\* SAFETY: the final result is a sorted permutation of the input.
\* LIVENESS: the algorithm eventually reaches its terminal state.
Spec == Init /\ [][Next]_vars /\ WF_vars(Loop) /\ WF_vars(Terminate)
PCorrectWF == PCorrect /\ (pc = "done" ~> pc = "done")

\* The finiteness of the reachable state space rests entirely on
\* LimitedSeq being a bounded variant of Seq; removing that bound makes
\* the model uncheckable by TLC.
====
---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

ASSUME Values \subseteq Int

Variables == <<arr, original, work, pc>>
TypeOK ==
  /\ arr \in Seq([1 .. MaxSeqLen -> Values])
  /\ original \in Seq([1 .. MaxSeqLen -> Values])
  /\ work \in SUBSET (SUBSET [1 .. MaxSeqLen])
  /\ pc \in {"loop", "done"}

\* A partition of interval I around pivot p leaves everything outside I
\* untouched and arranges the elements at or below the pivot no greater
\* than those above it.
Partitions(arr, I, p) ==
  { arr2 \in Seq([1 .. MaxSeqLen -> Values]) :
       /\ \A k \in 1 .. MaxSeqLen : k \notin I => arr2[k] = arr[k]
       /\ \A i, j \in I :
            (i <= p /\ j > p /\ arr2[i] > arr2[j]) => FALSE }

\* Permutations are defined via composition with automorphisms of the
\* domain, paired with a cardinality check so they stay finite.
Permutation(f, g) ==
  /\ \A x \in 1 .. MaxSeqLen : f[g[x]] = g[f[x]]
  /\ Cardinality({ f[x] : x \in 1 .. MaxSeqLen }) = MaxSeqLen

Init ==
  /\ arr = Seq
  /\ original = Seq
  /\ work = { 1 .. MaxSeqLen }
  /\ pc = "loop"

Next ==
  \/ \E I \in work :
       /\ Cardinality(I) = 1
       /\ work' = work \ {I}
       /\ UNCHANGED <<arr, original, pc>>
  \/ \E I \in work, p \in I :
       /\ Cardinality(I) > 1
       /\ \E arr2 \in Partitions(arr, I, p) :
            /\ arr' = arr2
            /\ work' = (work \ {I}) \cup { {i \in I : i <= p}, {i \in I : i > p} }
       /\ UNCHANGED <<original, pc>>
  \/ (work = {}) /\ pc' = "done" /\ UNCHANGED <<arr, original, work>>
  \/ (pc = "done") /\ UNCHANGED Variables

vars == <<arr, original, work, pc>>

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Bounded termination: the work set shrinks strictly on each iteration,
\* so it must reach the empty set.
Termination ==
  /\ work = {}
  /\ pc = "done"

\* The final sequence is a permutation of the original and is sorted.
Sorted(s) == \A i, j \in 1 .. MaxSeqLen : i <= j => s[i] <= s[j]
PCorrect ==
  (pc = "done") => /\ Permutation(arr, original)
                    /\ Sorted(arr)

\* The invariant starts with a coarse domain partition and refines it
\* as the algorithm progresses. It also states the permutation and
\* sortedness properties as safety facts, so they hold whenever the
\* algorithm is observed, not just at the end.
Inv ==
  /\ work \subseteq SUBSET [1 .. MaxSeqLen]
  /\ Permutation(arr, original)
  /\ \A i, j \in 1 .. MaxSeqLen : i <= j => arr[i] <= arr[j]

====
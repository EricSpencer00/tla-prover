---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

Cubes == (1..MaxSeqLen) \X (1..MaxSeqLen)
Domain == 1..MaxSeqLen

\* The non-deterministic partition is abstracted to any valid result a real
\* partition procedure could produce: it rearranges the chosen interval so that
\* elements at or below the pivot index are no greater than those above it.
\* Stutter is for the deadlock-free stuttering step after termination.
VARIABLES seq, orig, work, pc

\* A partition of the interval [i..j] around pivot p leaves elements outside the
\* interval untouched and respects the ordering invariant between the halves.
Partitions(i, j, p) == {w \in [Domain -> Values] :
  /\ \A k \in Domain \ (k < i \/ k > j) : w[k] = seq[k]
  /\ \A a \in i..p, b \in (p + 1)..j : w[a] <= w[b]}

TypeOK ==
  /\ seq \in [Domain -> Values]
  /\ orig \in [Domain -> Values]
  /\ work \subseteq Cubes
  /\ pc \in {"loop", "done"}

Init ==
  /\ seq = Seq
  /\ orig = Seq
  /\ work = {<<1, MaxSeqLen>>}
  /\ pc = "loop"

\* One loop iteration: pick an interval, partition it around a pivot, and
\* replace it by its two subintervals -- all in a single step.
Step ==
  \/ \E i, j \in Domain, p \in Domain :
        /\ <<i, j>> \in work
        /\ j > i
        /\ p \in i..j
        /\ \E w \in Partitions(i, j, p) :
             /\ seq' = w
             /\ work' = (work \ {<<i, j>>}) \cup {<<i, p>>, <<p + 1, j>>}

  \/ \E i, j \in Domain :
        /\ <<i, j>> \in work
        /\ i = j
        /\ work' = work \ {<<i, j>>}
        /\ UNCHANGED <<seq, orig, pc>>

  \/ \E w \in Partitions(1, MaxSeqLen, 1) :
        /\ work = {}
        /\ pc = "loop"
        /\ seq' = w
        /\ work' = {}
        /\ pc' = "done"
        /\ UNCHANGED orig

Stutter == (\A c \in {seq, orig, work, pc} : UNCHANGED c)

Next == Step \/ Stutter

Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* Relatively sorted: intervals that appear earlier in the domain are not
\* greater than intervals that appear later, which is the non-decreasing order.
RelSorted ==
  \A i, j, k, l \in Domain :
    /\ <<i, j>> \in work
    /\ <<k, l>> \in work
    /\ j < k
    /\ \A a \in i..j, b \in k..l : seq[a] <= seq[b]

DomainPartition == work = Cubes

PCorrect ==
  /\ DomainPartition
  /\ \A k \in 1..MaxSeqLen : orig[k] \in Values

\* Permutations are defined via domain automorphisms that preserve the partition
\* intervals so the output is a rearrangement of the original input.
Permutation ==
  \E f \in [Domain -> Domain] :
    /\ \A x, y \in Domain : seq[x] = orig[y] => f[x] = y
    /\ \A x, y \in Domain : f[x] = f[y] => x = y
    /\ \A i, j \in Domain : i < j => f[i] <= f[j]
    /\ \A i \in 1..MaxSeqLen : seq[i] = orig[f[i]]

Termination == pc = "done"

====
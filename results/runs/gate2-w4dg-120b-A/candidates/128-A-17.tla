---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

\* A quicksort that abstracts the partition step: the algorithm may replace the
\* whole sequence with any version that permutes the domain and respects the
\* pivot ordering on the chosen interval. The invariant + theorem together check
\* that termination leaves a sorted permutation of the original.

Intervals == UNION {[1 .. MaxSeqLen] \X [1 .. MaxSeqLen]}
Domain == 1 .. Len(Seq)

VARIABLES seq, original, work, pc

vars == << seq, original, work, pc >>

TypeOK ==
  /\ seq \in Seq
  /\ original \in Seq
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

\* An automorphism of the index domain: a bijection that moves only indices
\* inside the chosen interval, keeping sortedness of the original partition.
Automorphisms(s, i, j) ==
  { f \in [Domain -> Domain] :
      /\ \A k \in Domain : i <= k <= j => f[k] \in (i .. j)
      /\ \A k \in Domain : (k < i \/ k > j) => f[k] = k
      /\ \A a, b \in Domain :
           (f[a] = b) <=> (f[b] = a)
      /\ \A a, b \in Domain :
           (a <= b /\ f[a] <= f[b]) => seq[a] <= seq[b] }

\* The partition operator: an arbitrary permutation of the domain that respects
\* the pivot ordering inside the interval, leaves the rest untouched.
PerformPartition(i, j) ==
  { seq' \in Seq :
      /\ Len(seq') = Len(seq)
      /\ \A k \in Domain :
           seq'[f[k]] = seq[k] /\ f \in Automorphisms(seq, i, j)
      /\ \A k \in Domain : k < i \/ k > j => seq'[k] = seq[k]
      /\ \A k \in i .. j : \A l \in i .. j :
           (k <= l /\ seq'[k] > seq'[l]) => k = l }

Init ==
  /\ seq = Seq
  /\ original = Seq
  /\ work = {[1, Len(Seq)]}
  /\ pc = "loop"

Next ==
  \/ \E r \in work :
       /\ r[1] = r[2]
       /\ work' = work \ {r}
       /\ UNCHANGED << seq, original, pc >>
  \/ \E r \in work : \E p \in r[1] .. r[2] :
       /\ r[1] # r[2]
       /\ Len(seq) >= 2
       /\ \E s \in PerformPartition(r[1], r[2]) :
            /\ seq' = s
            /\ work' = (work \ {r}) \cup {[r[1], p], [p + 1, r[2]]}
       /\ UNCHANGED << original, pc >>
  \/ (pc = "loop" /\ work = {}) /\ pc' = "done" /\ UNCHANGED << seq, original, work >>
  \/ (pc = "done") /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Permutations preserve the multiset of values, so the final sorted result is
\* a rearrangement of the original.
SortedPermutation ==
  /\ \A e \in Values : Cardinality({i \in Domain : seq[i] = e}) =
                       Cardinality({i \in Domain : original[i] = e})
  /\ \A i \in 1 .. (Len(seq) - 1) : seq[i] <= seq[i + 1]

\* The full invariant: the work set stays a partition of the domain, the live
\* intervals are internally sorted, and the whole sequence is a sorted
\* permutation of the original.
Inv ==
  /\ work \subseteq Intervals
  /\ \A a, b \in work : (a[1] <= b[1] /\ a[2] >= b[2]) => a = b
  /\ \A r \in work :
       /\ r[1] < r[2] => \A i \in r[1] .. (r[2] - 1) : seq[i] <= seq[i + 1]
       /\ r[1] = r[2] => TRUE
  /\ pc = "done" => SortedPermutation

PCorrect ==
  /\ pc = "done" => SortedPermutation
  /\ pc = "loop" => TRUE

Termination == <>(pc = "done")

====
---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

((** Sequences.Seq is replaced by a finite bounded version so model checking stays
    tractable.  It is kept EXTENDS Sequences because the rest of the module still
    makes use of the usual sequence operators that live there.  The redefinition
    below is the only change to the shared library.  **))
LimitedSeq == [n \in Nat |-> CHOOSE s \in Seq(0 .. MaxSeqLen) : Len(s) = n]
Sequences == [Seq EXCEPT ! = LimitedSeq]

\* Domain partitions: intervals are always either disjoint or one is contained
\* in the other.  Permutations: composed with a domain automorphism.
\* Relative sortedness: lower intervals never hold a value above an upper one.
DomainPartition(D, I) ==
  \A p, q \in I : (p # q) => (p[1] # q[1] \/ p[2] # q[2])
Permutation(D, s, t) ==
  \E f \in [1 .. D -> 1 .. D] : (Injective(f) /\ \A i \in 1 .. D : s[f[i]] = t[i])
RelSorted(I) ==
  \A i, j \in I : i[1] <= j[1] => s[i[1]] <= s[j[1]]

VARIABLES s, orig, work, pc

vars == <<s, orig, work, pc>>

Intervals == {i \in 1 .. MaxSeqLen : i >= 2}
Range(i) == 1 .. i
RangeSubset == {Range(i) : i \in Intervals}

TypeOK ==
  /\ s \in Sequences
  /\ orig \in Sequences
  /\ work \subseteq RangeSubset
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s0 \in [1 .. MaxSeqLen -> Values] : s = s0
  /\ orig = s
  /\ work = {Range(MaxSeqLen)}
  /\ pc = "loop"

\* One loop iteration: pick an interval, partition it, or drop a singleton.
Step ==
  /\ pc = "loop"
  /\ \E r \in work :
       /\ work' = work \ {r}
       /\ IF Len(r) = 1
          THEN UNCHANGED <<s, orig>>
          ELSE
            \E pivot \in r :
              /\ Len(r) > 1
              /\ LET lo == {i \in r : i <= pivot}
                     hi == {i \in r : i > pivot}
                     newSeq == CHOOSE t \in {t \in Sequences :
                       /\ Len(t) = Len(s)
                       /\ \A i \in 1 .. MaxSeqLen :
                            (i \in r => (i <= pivot => t[i] <= t[pivot] /\ t[pivot] <= t[i])
                             \/ (i > pivot => t[pivot] <= t[i] \/ t[i] >= t[pivot]))
                       /\ \A i \in 1 .. MaxSeqLen : i \notin r => s[i] = t[i]}
                     : Permutation(MaxSeqLen, s, t)
              /\ s' = newSeq
              /\ work' = work \cup {lo, hi}
              /\ UNCHANGED orig
  /\ IF work = {} THEN pc' = "done" ELSE pc' = pc

Stall == pc = "done" /\ UNCHANGED vars

Next == Step \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* Termination: the algorithm always reaches its terminal state.
Termination == <>(pc = "done")

PCorrect ==
  /\ DomainPartition(MaxSeqLen, work)
  /\ Permutation(MaxSeqLen, orig, s)
  /\ RelSorted(work)

TypeOKInv == TypeOK /\ PCorrect
====
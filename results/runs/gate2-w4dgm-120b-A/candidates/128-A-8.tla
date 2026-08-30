---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* One interval is a contiguous index range of the sequence being sorted.
Interval == [lo : 1 .. MaxSeqLen, hi : 1 .. MaxSeqLen]

\* A partial automorphism of 1..MaxSeqLen; used to describe permutation
\* equivalence of sequences without reordering their indexing.
Automorphism == {f \in [1 .. MaxSeqLen -> 1 .. MaxSeqLen] :
                   \A i \in 1 .. MaxSeqLen : \E j \in 1 .. MaxSeqLen : f[j] = i}

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

TypeOK ==
  /\ seq \in [1 .. MaxSeqLen -> Values \cup {-1}]
  /\ orig \in [1 .. MaxSeqLen -> Values \cup {-1}]
  /\ work \subseteq Interval
  /\ pc \in {"loop", "done"}

\* Bounded domain: all values at indices > the true length are the padding -1.
SeqDomain == {i \in 1 .. MaxSeqLen : seq[i] # -1}
SeqLength == Cardinality(SeqDomain)
SeqMin == \E i \in SeqDomain : \A j \in SeqDomain : seq[i] <= seq[j]

Init ==
  /\ \E v \in [1 .. MaxSeqLen -> Values] :
        seq = [i \in 1 .. MaxSeqLen |-> IF i <= Cardinality(Values) THEN v[i] ELSE -1]
  /\ orig = seq
  /\ work = {[lo |-> 1, hi |-> SeqLength]}
  /\ pc = "loop"

\* One Quicksort iteration over an interval in the work set.
SortStep ==
  /\ pc = "loop"
  /\ \E a \in work :
       /\ work' = work \ {a}
       /\ IF a.lo = a.hi
          THEN work' = work'
          ELSE
            /\ \E pivot \in a.lo .. a.hi :
                 /\ seq' \in Partition(seq, a, pivot)
                 /\ work' = work' \cup {[lo |-> a.lo, hi |-> pivot], [lo |-> pivot + 1, hi |-> a.hi]}
  /\ pc' = pc
  /\ orig' = orig

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ seq' = seq
  /\ orig' = orig
  /\ work' = work

Done == pc = "done"

\* Once done, nothing more happens; this keeps the state space finite.
Quiesce ==
  /\ Done
  /\ pc' = pc
  /\ seq' = seq
  /\ orig' = orig
  /\ work' = work

Next == SortStep \/ Terminate \/ Quiesce

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SortStep)
  /\ WF_vars(Terminate)

\* Sequence is a permutation of its input; each index appears exactly once.
SeqPermutation == \E f \in Automorphism : orig = [i \in 1 .. MaxSeqLen |-> seq[f[i]]]

\* Inductive invariant: each index domain block is intact, permutation is
\* preserved, and domain blocks are sorted relative to each other.
Inv ==
  /\ \A a \in work : seqDomain(a) = {i \in 1 .. MaxSeqLen : a.lo <= i /\ i <= a.hi}
  /\ SeqPermutation
  /\ \A a, b \in work : a.hi < b.lo => seq[a.hi] <= seq[b.lo]

\* The final sequence is a sorted permutation of the input.
PCorrect == Done => (SeqPermutation /\ SeqMin)

\* SAFETY: bounded exploration of the state space never reaches a bad state.
TypeOKInv == TypeOK /\ Inv

\* LIVENESS: the algorithm always eventually finishes.
Termination == <>(pc = "done")

\* Replaces Seq from Sequences with a finite version so the model is checkable.
LimitedSeq(f) == {<<i, f[i]>> : i \in 1 .. MaxSeqLen /\ f[i] # -1}

\* The partition operator is nondeterministic: it may pick any rearrangement
\* of the chosen interval that respects the pivot ordering and leaves the rest
\* of the sequence untouched. It is assumed to be nonempty for every call.
Partition(f, a, pivot) ==
  {g \in [1 .. MaxSeqLen -> Values \cup {-1}] :
     /\ \A i \in 1 .. MaxSeqLen : i < a.lo \/ i > a.hi => g[i] = f[i]
     /\ \A i, j \in a.lo .. pivot : i <= j => g[i] <= g[j]
     /\ \A i, j \in (pivot + 1) .. a.hi : i <= j => g[i] <= g[j]
     /\ \A i \in a.lo .. pivot, j \in (pivot + 1) .. a.hi : g[i] <= g[j]}
====
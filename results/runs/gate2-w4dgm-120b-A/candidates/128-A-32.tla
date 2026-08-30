---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, Permutations

CONSTANTS Values, MaxSeqLen

\* Operators inherited from Sequences, redefined here for a finite model.
\* Replaced: Seq   (FiniteSeq is the checkable, truncated version.)
LimitedSeq(S) == CHOOSE s \in Seq(S) : \A i \in DOMAIN s : s[i] \in S /\ Len(s) <= MaxSeqLen
RestrictedSeq == LimitedSeq(S)

T = "done"

VARIABLES seq, originalSeq, worklist, pc
vars == <<seq, originalSeq, worklist, pc>>

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
\* A partition respects the interval's boundary and the pivot's split point.
ValidPartition(s, i, p) ==
  /\ \A k \in 1..MaxSeqLen : (k < i.lo \/ k > i.hi) => s[k] = seq[k]
  /\ \A k \in i.lo..i.hi : (k <= p => s[k] <= s[p]) /\ (k >= p => s[k] >= s[p])

Init ==
  /\ \E s \in RestrictedSeq : seq = originalSeq = s
  /\ worklist = {[lo |-> 1, hi |-> Len(seq]]}
  /\ pc = "main"

SelectInterval(i, p) ==
  /\ i \in worklist
  /\ i.lo < i.hi
  /\ \E s \in { t \in RestrictedSeq : ValidPartition(t, i, p) } : seq' = s
  /\ worklist' = (worklist \ {i}) \cup {[lo |-> i.lo, hi |-> p], [lo |-> p, hi |-> i.hi]}
  /\ pc' = pc

SublistSorted(i) ==
  /\ i \in worklist
  /\ i.lo = i.hi
  /\ worklist' = worklist \ {i}
  /\ pc' = pc
  /\ UNCHANGED seq
  /\ UNCHANGED originalSeq

Terminate ==
  /\ worklist = {}
  /\ pc' = T
  /\ UNCHANGED <<seq, originalSeq, worklist>>

Idle == UNCHANGED vars

Next ==
  \/ \E i \in Intervals, p \in 1..MaxSeqLen : SelectInterval(i, p)
  \/ \E i \in Intervals : SublistSorted(i)
  \/ Terminate
  \/ Idle

Spec == Init /\ [][Next]_vars
          /\ (\A i \in Intervals, p \in 1..MaxSeqLen : SF_vars(SelectInterval(i, p)))
          /\ (\A i \in Intervals : WF_vars(SublistSorted(i)))
          /\ WF_vars(Terminate)

\* Permutation of the original, plus sortedness across the whole array.
PCorrect ==
  /\ \E f \in ((1..MaxSeqLen) -- domain(seq)) \cup (domain(seq) >-> domain(seq)) :
       \A k \in domain(seq) : seq[k] = originalSeq[f[k]]
  /\ \A i \in domain(seq) : (i + 1 \in domain(seq)) => (seq[i] <= seq[i + 1])

TypeOK ==
  /\ seq \in RestrictedSeq
  /\ originalSeq \in RestrictedSeq
  /\ worklist \subseteq Intervals
  /\ pc \in {"main", T}

\* Worklist is always a partition of the domain; each split respects ordering.
Inv ==
  /\ UNION { {k \in domain(seq) : i.lo <= k /\ k <= i.hi} : i \in worklist } = domain(seq)
  /\ \A i \in worklist : \A j \in worklist : i # j => ~ (i.lo <= j.hi /\ j.lo <= i.hi)
  /\ \A i \in worklist : \A k \in i.lo..i.hi : k < Len(seq) => seq[k] <= seq[k + 1]

Termination == <> (pc = T)
====
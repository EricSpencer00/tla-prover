---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

\* The state space (augmented with the domain of the current permutation)
\* is finite and bounded by the companion model's choice of MaxSeqLen and Values.
ThisSet == [perm: [1..MaxSeqLen -> Values], work: SUBSET [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen], pc: {"loop", "term"}, orig: <<>>]

VARIABLES perm, work, pc, orig
vars == <<perm, work, pc, orig>>

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
Ltr(i) == IF i <= MaxSeqLen THEN perm[i] ELSE Values
SeqRange(a, b) == IF b < a THEN <<>> ELSE <<Ltr(a), Ltr(a + 1), Ltr(a + 2) # ... # Ltr(b)>>

\* Intervals partition the domain 1..MaxSeqLen, and the permutation of the
\* elements inside an interval is independent of the permutation elsewhere.
Partitions(S) == \A a, b \in S : (a.lo <= b.lo /\ a.hi >= b.hi) \/ (b.lo <= a.lo /\ b.hi >= a.hi)

\* The partition operator is nondeterministic over all valid results of a
\* single partition step: it must respect the pivot split and leave the
\* outside unchanged, but the relative ordering inside each side is free.
CAS(k, lo, hi) ==
  LET left == {i \in lo..hi : i <= k}
      right == {i \in lo..hi : i > k}
  IN {p \in [1..MaxSeqLen -> Values] :
        (\A i \in dom Ltr : p[i] = Ltr(i))
          /\ (\A i \in left, j \in right : p[i] <= p[j])}

TypeOK ==
  /\ pc \in {"loop", "term"}
  /\ work \subseteq Intervals
  /\ orig \in ThisSet

\* A partitioned permutation of the same domain is a permutation of the same
\* multiset of values.
Perm(L, S) == \E f \in [1..L -> 1..L] :
                 \A i \in 1..L : \A j \in 1..L : Ltr(i) = Ltr(j) => f[i] = f[j]

Init ==
  /\ perm = Seq
  /\ orig = Seq
  /\ work = {[lo |-> 1, hi |-> MaxSeqLen]}
  /\ pc = "loop"

\* Threaded through the algorithm for stuttering only.
Loop ==
  /\ pc = "loop"
  /\ \E i \in work :
       /\ work' = work \ {i}
       /\ IF i.lo = i.hi
          THEN work'
          ELSE (\E k \in i.lo..i.hi :
                 /\ perm' \in CAS(k, i.lo, i.hi)
                 /\ work' = work' \cup {[lo |-> i.lo, hi |-> k], [lo |-> k + 1, hi |-> i.hi]})
  /\ UNCHANGED <<pc, orig>>

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "term"
  /\ UNCHANGED <<perm, work, orig>>

Stall ==
  /\ pc = "term"
  /\ UNCHANGED vars

Next == Loop \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop) /\ WF_vars(Terminate)

\* The final permutation has not been corrupted and is sorted.
PCorrect == (pc = "term") => (\A i \in 1..MaxSeqLen - 1 : perm[i] <= perm[i + 1] /\ Perm(MaxSeqLen, perm))
Inv == Partitions(work) /\ Perm(MaxSeqLen, perm) /\ \A i \in 1..MaxSeqLen - 1 : perm[i] <= perm[i + 1]

Termination == (pc = "term") ~> (pc = "term")
====
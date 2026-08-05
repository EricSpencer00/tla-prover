---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

VARIABLES seq, originalSeq, workSet, pc
vars == <<seq, originalSeq, workSet, pc>>

SeqDomain == {1 .. Len(seq)}
Interval == [low: 1 .. MaxSeqLen, high: 1 .. MaxSeqLen]
DomainPermutations ==
  {f \in [SeqDomain -> SeqDomain] : \A x \in SeqDomain : f[f[x]] = x}
Automorphisms == {f \in DomainPermutations : \A x \in SeqDomain : x <= f[x]}
SortedOn(f, S) == \A x, y \in S : x < y => f[x] <= f[y]

Permutation(s, t) == \E f \in Automorphisms : \A x \in SeqDomain : t[x] = s[f[x]]

VALID(n, lo, hi) == lo <= n /\ n <= hi
Bounded(i) == i \in 1 .. MaxSeqLen

RelativelySorted == \A i, j \in SeqDomain : i < j => seq[i] <= seq[j]

TypeOK ==
  /\ seq \in Seq(Values)
  /\ originalSeq \in Seq(Values)
  /\ workSet \subseteq [low: 1 .. MaxSeqLen, high: 1 .. MaxSeqLen]
  /\ pc \in {"loop", "halt"}

Init ==
  /\ \E s \in Seq(Values) : s # <<>> /\ seq = s /\ originalSeq = s
  /\ workSet = {[low |-> 1, high |-> Len(seq)]}
  /\ pc = "loop"

PartitionStep(a, lo, hi, n) ==
  \E t \in Permutation(seq, <<>>) :
     /\ Permutation(seq, t)
     /\ \A i \in SeqDomain : (i < lo \/ i > hi \/ i = n) => t[i] = seq[i]
     /\ \A i \in SeqDomain : VALID(i, lo, n) => \A j \in SeqDomain : VALID(j, n + 1, hi) => t[i] <= t[j]
     /\ seq' = t
  /\ workSet' = (workSet \ {[low |-> lo, high |-> hi]}) \cup {[low |-> lo, high |-> n], [low |-> n + 1, high |-> hi]}

QuicksortStep ==
  \/ IF pc = "loop" /\ workSet # {}
       THEN \E i \in workSet :
              IF i.low = i.high
                THEN workSet' = workSet \ {i}
                ELSE \E n \in SeqDomain : VALID(n, i.low, i.high) /\ PartitionStep(i.low, i.high, n)
                /\ UNCHANGED <<seq, originalSeq>>
       ELSE UNCHANGED <<seq, originalSeq, workSet, pc>>
     /\ pc' = IF workSet = {} THEN "halt" ELSE "loop"
  \/ (pc = "halt" /\ UNCHANGED vars)

Spec == Init /\ [][QuicksortStep]_vars /\ WF_vars(QuicksortStep)

PCorrect == pc = "halt" => (Permutation(originalSeq, seq) /\ RelativelySorted)

Inv == /\ workSet \subseteq {[low: 1 .. MaxSeqLen, high: 1 .. MaxSeqLen]}
       /\ originalSeq \in Seq(Values) /\ seq \in Seq(Values)
       /\ RelativelySorted

Termination == <>(pc = "halt")

\* LimitedSeq is the bounded-version of the Seq operator from the standard module,
\* overridden here so the state space stays finite during model checking.
LimitedSeq ==
  {s \in Seq(Values) : Len(s) <= MaxSeqLen}
====
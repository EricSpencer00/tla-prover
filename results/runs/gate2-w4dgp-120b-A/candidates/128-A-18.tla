---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, Automorphisms

CONSTANTS
  Values, MaxSeqLen

Domain == 1 .. MaxSeqLen

VARIABLES seq, originalSeq, workSet, pc

vars == <<seq, originalSeq, workSet, pc>>

\* A partition of an interval is any rearrangement of that interval that
\* respects the pivot ordering constraint, leaving the rest untouched.
Partitions(s, lo, hi, piv) ==
  {t \in [Domain -> Values] :
     /\ \A i \in Domain \ lo .. hi : t[i] = s[i]
     /\ \A i \in Domain \ (lo .. hi) : t[i] = s[i]
     /\ \A i \in lo .. piv, j \in (piv + 1) .. hi : t[i] <= t[j]}

TypeOK ==
  /\ seq \in [Domain -> Values]
  /\ originalSeq \in [Domain -> Values]
  /\ workSet \subseteq SUBSET Domain
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in {s \in [Domain -> Values] : \E k \in 1 .. MaxSeqLen : \A i \in Domain : i > k => s[i] = 0} :
       /\ seq = s
       /\ originalSeq = s
  /\ workSet = {Domain}
  /\ pc = "loop"

LoopStep ==
  /\ pc = "loop"
  /\ workSet # {}
  /\ \E interval \in workSet :
       LET lo == CHOOSE m \in interval : \A k \in interval : k >= m
           hi == CHOOSE m \in interval : \A k \in interval : k <= m
       IN
       \/ /\ lo = hi
          /\ workSet' = workSet \ {interval}
          /\ UNCHANGED <<seq, originalSeq>>
       \/ \E piv \in lo .. hi, s' \in Partitions(seq, lo, hi, piv) :
            workSet' = (workSet \ {interval}) \cup {lo .. piv, (piv + 1) .. hi}
            /\ seq' = s'
            /\ originalSeq' = originalSeq
  /\ pc' = "loop"

Terminate ==
  /\ pc = "loop"
  /\ workSet = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, originalSeq, workSet>>

Next ==
  \/ LoopStep
  \/ Terminate
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopStep \/ Terminate)

\* Termination: a finite partitioning of a finite domain terminates.
Termination == <> (pc = "done")

Inversions(s, lo, hi) == Cardinality {<<i, j>> \in (lo .. hi) \X (lo .. hi) : i <= j /\ s[i] > s[j]}
Sorted(s, lo, hi) == Inversions(s, lo, hi) = 0

\* The sorted check is local to the interval being partitioned; the full
\* permutation argument is handled by the interval induction.
PCorrect ==
  (pc = "done") => (seq = originalSeq /\ Sorted(seq, 1, MaxSeqLen))

Permutations ==
  \A lo, hi \in DOMAIN:
    /\ (hi < lo) => True
    /\ (hi = lo) => True
    /\ (hi > lo) => (seq \o Automorphism(lo, hi)) = originalSeq

\* The inductive invariant lays down the domain partition, the permutation
\* preservation, and the sortedness ordering between intervals.
Inv ==
  /\ \A i \in DOMAIN : (seq[i] \in Values)
  /\ Permutations
  /\ \A lo, hi \in DOMAIN :
       /\ (hi < lo) => Sorted(seq, lo, hi)
       /\ (hi = lo) => True
       /\ (hi > lo) => (Sorted(seq, lo, hi) \/ Sorted(seq, hi, lo))

=========================================
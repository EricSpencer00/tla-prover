---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

Intervals == UNION {[i..j]: i, j \in 1..MaxSeqLen}
Indices == 1..MaxSeqLen

VARIABLES seq, origSeq, work, pc
vars == <<seq, origSeq, work, pc>>

\* A bounded version of the sequence operator, used by the .cfg to keep the
\* model finite; definition is required here because the .cfg replaces Seq.
LimitedSeq(S) == CHOOSE f \in [1..MaxSeqLen -> S \cup {MaxSeqLen}]:
                    \A i \in 1..MaxSeqLen : f[i] # MaxSeqLen => f[i] \in S

TypeOK ==
  /\ seq \in Seq(Values)
  /\ origSeq \in Seq(Values)
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in Seq(Values) :
       /\ s # << >>
       /\ Len(s) <= MaxSeqLen
       /\ seq = LimitedSeq(s)
       /\ origSeq = LimitedSeq(s)
  /\ work = {1..Len(seq)}
  /\ pc = "loop"

\* Permutations of the domain; used to express that the final sequence is a
\* rearrangement of the original and nothing is lost or fabricated.
Dom == 1..MaxSeqLen
DomainPermutations == {g \in [Dom -> Dom] : \A x, y \in Dom : g[x] = g[y] => x = y}

PermutationOfOriginal(t) ==
  /\ Len(t) = Len(origSeq)
  /\ \E g \in DomainPermutations :
       \A i \in 1..Len(t) : t[i] = origSeq[g[i]]

RecursivePartition(a, b, k) ==
  /\ k \in a..b
  /\ a \in Intervals
  /\ b \in Intervals
  /\ a <= k
  /\ k < b
  /\ [a..b] \in Intervals
  /\ [a..k] \in Intervals
  /\ [k+1..b] \in Intervals

\* The partition operator is nondeterministic over the set of all valid
\* partition outcomes for the chosen interval and pivot.
ValidPartitions(a, b, k, seq) ==
  { t \in Seq(Values) :
      /\ Len(t) = Len(seq)
      /\ \A i \in 1..Len(t) :
            (i < a \/ i > b) => t[i] = seq[i]
      /\ \A i, j \in a..b :
            (i <= k /\ j > k) => t[i] <= t[j]
  }

Step ==
  /\ pc = "loop"
  /\ \E a \in Intervals :
       /\ a \in work
       /\ Len(seq) \in a
       /\ IF Len(seq) = 1 \/ a = {Len(seq)} THEN
            work' = work \ {a}
          ELSE
            \E k \in a..(Len(seq) - 1) :
              /\ RecursivePartition(a, Len(seq), k)
              /\ \E t \in ValidPartitions(a, Len(seq), k, seq) : seq' = t
              /\ work' = (work \ {a}) \cup {a..k, (k+1)..Len(seq)}
       /\ UNCHANGED <<origSeq, pc>>
  \/ pc' = IF work = {} THEN "done" ELSE pc

Quiesce ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* Partial correctness: termination implies a sorted permutation of the input.
PCorrect ==
  (pc = "done") =>
    /\ PermutationOfOriginal(seq)
    /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

\* Stronger inductive invariant relating sortedness to the interval partition:
\* everything below a partition point is no greater than everything above it.
Inv ==
  /\ PermutationOfOriginal(seq)
  /\ \A a, b \in Intervals :
        (a \in work /\ b \in work /\ a # b /\ a \cup b = work) => \A i \in a, j \in b : seq[i] <= seq[j]

Termination == (pc = "loop") ~> (pc = "done")

====
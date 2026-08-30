---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANTS Values, MaxSeqLen

\* One sort action: it picks a whole interval and partitions it in one step,
\* which is the abstraction over the actual partition procedure.
VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

Ranges == union {[1..n -> Values] : n \in 1..MaxSeqLen}
Domain(f) == {f[i] : i \in 1..Len(f)}
Within(x, f) == \E i \in 1..Len(f) : f[i] = x

TypeOK ==
  /\ seq \in Ranges
  /\ orig \in Ranges
  /\ work \subseteq (1..MaxSeqLen) \X (1..MaxSeqLen)
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E e \in Ranges : seq = e /\ orig = e
  /\ work = {(1, MaxSeqLen)}
  /\ pc = "loop"

\* Work is intervals; partitioning replaces an interval with two subintervals.
SortStep ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E i \in work :
       /\ i[1] = i[2]
          => work' = work \ {i}
       /\ i[1] < i[2]
          /\ \E p \in i[1]..i[2] :
               /\ \E s \in PartitionOperators(seq, i, p) :
                    /\ seq' = s
               /\ LET lo == <<i[1], p>> IN
                  LET hi == <<p + 1, i[2]>> IN
                    work' = (work \ {i}) \cup {lo, hi}
  /\ UNCHANGED orig /\ pc'

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Stall == UNCHANGED vars

Next == SortStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(SortStep)

\* The invariant is a partition of the domain: each bucket is below its
\* sibling, and the whole range is still a permutation of the input.
Inv ==
  /\ {i \in 1..MaxSeqLen : i + 1 \in 1..Len(seq) /\ seq[i] > seq[i + 1]} = {}
  /\ Domain(seq) = Domain(orig)
  /\ \A a, b \in 1..Len(seq) : seq[a] = seq[b] => a = b

\* Permutation equivalence is defined via composition with a bijection.
PermutationsOf ==
  {g \in (1..MaxSeqLen -> 1..MaxSeqLen) :
     \A a, b \in 1..MaxSeqLen : g[a] = g[b] => a = b}
PermutationOf(s) == \E g \in PermutationsOf : s = [i \in 1..Len(seq) |-> orig[g[i]]]

PCorrect ==
  /\ pc = "done" => PermutationOf(seq)
  /\ \A i \in 1..MaxSeqLen - 1 : seq[i] > seq[i + 1] => i + 1 > Len(seq)

Termination == <>(pc = "done")

\* Finite version of Seq for model checking: it fails on too-long arguments.
LimitedSeq(x) == IF Len(x) > MaxSeqLen THEN CHOOSE y \in Ranges : TRUE ELSE x
====
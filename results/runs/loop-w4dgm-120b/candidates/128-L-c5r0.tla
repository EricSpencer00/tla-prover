---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets

CONSTANTS Values, MaxSeqLen

Seq == LimitedSeq
Range(s) == { s[i] : i \in 1..Len(s) }

Interval == { i \in 1..MaxSeqLen : TRUE }
SubIntervals(iv, k) ==
  let low == {i \in iv : i <= k} high == {i \in iv : i > k} in
  IF low = {} \/ high = {} THEN {iv} ELSE {low, high}

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

TypeOK ==
  /\ seq \in Seq
  /\ orig \in Seq
  /\ work \subseteq Interval
  /\ pc \in {"loop", "done"}

OnlyPartitions ==
  /\ \A iv \in work : iv \subseteq 1..Len(seq)
  /\ \A i \in 1..Len(seq) : ~Cardinality({iv \in work : i \in iv}) = 1

PermutationOrigin ==
  \E g \in [1..Len(seq) -> 1..Len(seq)] :
    /\ \A i \in 1..Len(seq) : g[i] \in 1..Len(seq)
    /\ \A i, j \in 1..Len(seq) : g[i] = g[j] => i = j
    /\ seq = [i \in 1..Len(seq) |-> orig[g[i]]]

RelativeSortedness ==
  \A x \in work, y \in work :
    (x \cap y = {} /\ (x \cup y) \subseteq 1..Len(seq)) =>
      \A i \in x, j \in y : (i < j) => seq[i] <= seq[j]

Init ==
  /\ \E s \in Seq : /\ seq = s /\ orig = s
                    /\ Len(s) \in 1..MaxSeqLen
                    /\ \A i \in 1..Len(s), j \in 1..Len(s) : s[i] \in Values
  /\ work = {1..MaxSeqLen}
  /\ pc = "loop"

LoopStep ==
  /\ work # {}
  /\ \E iv \in work :
       /\ work' = work \ {iv}
       /\ IF Cardinality(iv) = 1
            THEN work' = work \ {iv}
            ELSE \E k \in iv :
                   /\ work' = (work \ {iv}) \cup SubIntervals(iv, k)
                   /\ seq' = CHOOSE s \in seq \in SubSequences(ii \in 1..MaxSeqLen :
                        /\ ii \in iv => s[ii] <= s[k] \/ s[ii] >= s[k]
                        /\ ii \notin iv => s[ii] = seq[ii]
                        /\ \A i, j \in iv : (i <= k /\ j > k) => s[i] <= s[j])
  /\ pc' = pc
  /\ UNCHANGED orig

Terminate ==
  /\ work = {}
  /\ pc = "loop"
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Quiesce ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == LoopStep \/ Terminate \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopStep)

PCorrect == PermutationOrigin /\ RelativeSortedness
TypeOKOK == TypeOK /\ OnlyPartitions
Termination == <>(pc = "done")
====
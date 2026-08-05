---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, Permutations

(* The set of values is left abstract in the main module; a companion .cfg    *)
(* or .cfg-replacement sets it to a concrete finite subset of the integers.  *)
CONSTANTS Values, MaxSeqLen

\* A bounded version of Seq for model checking; the real Quicksort.tla defines
\* the operator below, so Seq is deliberately omitted from the EXTENDS set.
VARIABLES seq, original, intervals, pc

TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) >= 1
  /\ Len(seq) <= MaxSeqLen
  /\ original \in Seq(Values)
  /\ intervals \subseteq (1 .. MaxSeqLen) \X (1 .. MaxSeqLen)
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in Seq(Values) :
       /\ Len(s) >= 1
       /\ Len(s) <= MaxSeqLen
       /\ seq = s
       /\ original = s
  /\ intervals = {<<1, MaxSeqLen>>}
  /\ pc = "loop"

\* The partition step is abstracted as a nondeterministic choice of any
\* sequence that could validly result from a partition on the chosen pivot.
ValidPartitions(i, j) ==
  {t \in Seq(Values) |
     /\ Len(t) = Len(seq)
     /\ \A k \in (i .. j) : t[k] <= t[j]
     /\ \A k \in (j + 1 .. Len(seq)) : t[k] >= t[j]
     /\ \A k \in (1 .. i - 1) \cup (j + 1 .. Len(seq)) : t[k] = seq[k]}

LoopStep ==
  /\ pc = "loop"
  /\ intervals # {}
  /\ \E r \in intervals :
       /\ intervals' = intervals \ {r}
       /\ IF r[1] = r[2] THEN UNCHANGED <<seq, intervals>>
       /\ LET i == r[1]
              j == r[2]
              low == <<i, j - 1>>
              high == <<j + 1, r[2]>>
          IN \/ \E t \in ValidPartitions(i, j) :
                /\ seq' = t
                /\ intervals' = intervals \cup (IF j > i + 1 THEN {low} ELSE {})
                                                \cup (IF j + 1 < r[2] THEN {high} ELSE {})
          \/ /\ intervals = intervals \cup (IF j > i + 1 THEN {low} ELSE {})
                                    \cup (IF j + 1 < r[2] THEN {high} ELSE {})
             /\ UNCHANGED seq

Terminate ==
  /\ pc = "loop"
  /\ intervals = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, original, intervals>>

Quiesce ==
  /\ pc = "done"
  /\ UNCHANGED <<seq, original, intervals, pc>>

Next == LoopStep \/ Terminate \/ Quiesce

Spec == Init /\ [][Next]_<<seq, original, intervals, pc>>
           /\ WF_vars(LoopStep) /\ WF_vars(Terminate)

\* When the sort finishes, seq is both a permutation of the input and
\* sorted in non-decreasing order.
Sorted(s) == \A i \in DOMAIN s : \A j \in DOMAIN s : i < j => s[i] <= s[j]

PCorrect == pc = "done" => (seq \in Permutations(original) /\ Sorted(seq))

\* The invariant is split for readability: a partition only ever reorders
\* elements inside the pivot interval, each interval is a true domain piece,
\* and any element belonging to a lower interval is not greater than one
\* belonging to a higher interval, so the whole sequence is sorted when the
\* intervals are all singletons.
Inv ==
  /\ \A i, j \in 1 .. MaxSeqLen :
       /\ <<i, j>> \in intervals => i <= j
       /\ i <= j => seq[i] <= seq[j]
  /\ \A i, j \in 1 .. MaxSeqLen :
       /\ i <= j /\ <<i, j>> \in intervals
       => \A k \in DOMAIN seq :
            i <= k /\ k <= j => seq[k] = original[k]

Termination == TRUE ~> (pc = "done")

DomainPartition ==
  \A m, n \in 1 .. MaxSeqLen :
    <<m, n>> \in intervals => DOMAIN seq = 1 .. n

PermutationPreserved ==
  \A m, n \in 1 .. MaxSeqLen :
    <<m, n>> \in intervals => seq \in Permutations(original)

RelativeSorted ==
  \A m, n, p, q \in 1 .. MaxSeqLen :
    /\ <<m, n>> \in intervals
    /\ <<p, q>> \in intervals
    /\ n < p => seq[n] <= seq[p]
    /\ q < m => seq[q] <= seq[m]

====
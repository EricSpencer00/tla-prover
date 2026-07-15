---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (instantiated in the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen, Seq

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
Len == Len(Seq)

\* Intervals are represented as records with fields "l" (left index) and
\* "r" (right index), both inclusive.  The set of all possible intervals
\* that fit inside the sequence is:
AllIntervals == { [l |-> i, r |-> j] :
                    i \in 1..Len,
                    j \in i..Len }

\* Index set of the current sequence
Idx == 1..Len

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
IntervalIsSingleton(i) == i.l = i.r

\* A permutation of a sequence is a bijective mapping of its indices that
\* preserves the multiset of values.
Permutations(s) ==
  { t \in Seq : 
      \A j \in Idx: Count({k \in Idx: s[k] = t[j]}, Values) =
                   Count({k \in Idx: s[k] = s[j]}, Values) }

\* All elements of a sequence belong to Values
SeqValues(s) == \A i \in Idx: s[i] \in Values

\* ----------------------------------------------------------------------
\* Partition definition
\* ----------------------------------------------------------------------
\* Given an interval i and a pivot index p (i.l <= p <= i.r), a valid
\* partition of the current sequence "seq" is any sequence "newSeq"
\* such that
\*   1. Elements outside i are unchanged.
\*   2. For every index j <= p within i, newSeq[j] <= newSeq[p].
\*   3. For every index j > p within i, newSeq[j] >= newSeq[p].
\*   4. The multiset of values inside i is unchanged.
ValidPartition(i, p, newSeq) ==
  /\ \A j \in Idx: (j < i.l \/ j > i.r) => newSeq[j] = seq[j]
  /\ \A j \in i.l .. p:   newSeq[j] <= newSeq[p]
  /\ \A j \in p+1 .. i.r: newSeq[j] >= newSeq[p]
  /\ \A v \in Values:
        Cardinality({ j \in i.l .. i.r: seq[j] = v }) =
        Cardinality({ j \in i.l .. i.r: newSeq[j] = v })

\* ----------------------------------------------------------------------
\* TypeOK invariant (required)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in Seq /\ orig \in Seq
  /\ \A i \in Idx: seq[i] \in Values /\ orig[i] \in Values
  /\ work \subseteq AllIntervals
  /\ pc \in {"Running", "Terminated"}

\* ----------------------------------------------------------------------
\* Partial correctness invariant (required)
\* ----------------------------------------------------------------------
PCorrect ==
  /\ pc = "Terminated"
  /\ \A i \in Idx: seq[i] <= seq[i+1]  \* sortedness, with vacuous truth at end
  /\ \E perm \in Permutations(orig): \A i \in Idx: seq[i] = perm[i]

\* ----------------------------------------------------------------------
\* Full invariant used for model checking (required)
\* ----------------------------------------------------------------------
Inv == 
  /\ TypeOK
  /\ IF pc = "Terminated" THEN PCorrect ELSE TRUE

\* ----------------------------------------------------------------------
\* Initialization (required)
\* ----------------------------------------------------------------------
Init ==
  /\ seq = Seq
  /\ orig = Seq
  /\ work = { [l |-> 1, r |-> Len] }
  /\ pc = "Running"
  /\ TypeOK

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ProcessInterval ==
  /\ pc = "Running"
  /\ work # {}
  /\ \E i \in work:
        /\ IF IntervalIsSingleton(i) THEN
              /\ work' = work \ {i}
              /\ UNCHANGED <<seq, orig, pc>>
        ELSE
              /\ \E p \in i.l .. i.r:
                    /\ \E newSeq \in Seq:
                         /\ ValidPartition(i, p, newSeq)
                         /\ seq' = newSeq
                         /\ work' = (work \ {i}) \cup
                                    { [l |-> i.l, r |-> p],
                                      [l |-> p+1, r |-> i.r] }
                         /\ UNCHANGED <<orig, pc>>
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "Running"
  /\ work = {}
  /\ pc' = "Terminated"
  /\ UNCHANGED <<seq, orig, work>>

Stutter ==
  /\ pc = "Terminated"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
  \/ ProcessInterval
  \/ Terminate
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification (required)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Theorems and properties (required)
\* ----------------------------------------------------------------------
THEOREM InvIsInvariant == Spec => []Inv

Termination == Spec => []<>(pc = "Terminated")

====
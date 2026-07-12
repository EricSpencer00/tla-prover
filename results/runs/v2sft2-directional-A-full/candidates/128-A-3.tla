---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen, Seq

VARIABLES seq, orig, work, pc

\* Helper definitions
Len == Len(seq)

\* Interval is a record with fields low and high
\* We define a predicate IsInterval that checks low <= high and within bounds
IsInterval(I) == I.low <= I.high /\ 1 <= I.low /\ I.high <= Len

\* Set of all intervals over current seq
IntervalSet == { [low |-> i, high |-> j] : 1 <= i /\ i <= j /\ j <= Len }

FullInterval == [low |-> 1, high |-> Len]

Indices(I) == { i : I.low <= i /\ i <= I.high }

\* Count number of occurrences of a value v in seq over interval I
Count(seq, I, v) == Cardinality({ i : i \in Indices(I) /\ seq[i] = v })

\* Predicate that seq2 is a permutation of seq over I
Permutation(seq1, seq2, I) == 
   \A v \in Values : Count(seq1, I, v) = Count(seq2, I, v)

\* Relative sorted condition: every element at or before pivot <= every element after pivot
RelativeSort(newSeq, I, p) == 
   \A i, j \in 1..Len :
      (I.low <= i /\ i <= p /\ p+1 <= j /\ j <= I.high) => newSeq[i] <= newSeq[j]

\* PartitionResult: newSeq is a valid partition of seq over I using pivot p
PartitionResult(newSeq, I, p) ==
   /\ newSeq \in Seq
   /\ I.low <= p /\ p <= I.high
   /\ \A i \in 1..Len :
        (i < I.low \/ i > I.high) => newSeq[i] = seq[i]
   /\ Permutation(seq, newSeq, I)
   /\ RelativeSort(newSeq, I, p)

\* Subintervals created by splitting I at pivot p
LowerSubinterval(I, p) ==
   IF I.low <= p-1 THEN { [low |-> I.low, high |-> p-1] } ELSE {}

UpperSubinterval(I, p) ==
   IF p+1 <= I.high THEN { [low |-> p+1, high |-> I.high] } ELSE {}

\* Initial state
Init ==
   /\ seq \in Seq
   /\ orig = seq
   /\ work = { [low |-> 1, high |-> Len] }
   /\ pc = "Main"

\* Work step when work set is non-empty
WorkStep ==
   /\ pc = "Main"
   /\ work # {}
   /\ \E I \in work :
        /\ I \in IntervalSet
        /\ IF I.low = I.high THEN
             /\ work' = work \ {I}
             /\ UNCHANGED <<seq, orig, pc>>
           ELSE
             /\ \E p \in I.low .. I.high :
                    /\ \E newSeq \in Seq :
                          /\ PartitionResult(newSeq, I, p)
                          /\ work' = (work \ {I}) \cup
                                       LowerSubinterval(I, p) \cup
                                       UpperSubinterval(I, p)
                          /\ seq' = newSeq
                          /\ UNCHANGED <<orig, pc>>

\* Termination action
Terminate ==
   /\ pc = "Main"
   /\ work = {}
   /\ pc' = "Terminated"
   /\ UNCHANGED <<seq, orig, work>>

\* Stutter step after termination
Stutter ==
   /\ pc = "Terminated"
   /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
   WorkStep \/ Terminate \/ Stutter

Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* Safety invariants
TypeOK ==
   /\ seq \in Seq
   /\ orig \in Seq
   /\ work \subseteq IntervalSet
   /\ pc \in {"Main", "Terminated"}

PCorrect ==
   pc = "Terminated" => (Sorted(seq) /\ Permutation(orig, seq, FullInterval))

Inv ==
   (pc = "Terminated" => (Sorted(seq) /\ Permutation(orig, seq, FullInterval))) 
   /\ (work \subseteq IntervalSet)

\* Liveness property
Termination == <> (pc = "Terminated")

====
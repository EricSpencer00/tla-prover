---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\*  Operator that replaces Seq with a finite version for model checking
\* ----------------------------------------------------------------------
LimitedSeq(V) == { s \in Seq(V) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\*  Helper definitions
\* ----------------------------------------------------------------------
\* Intervals that can appear for a given sequence length
Intervals(s) == { <<i, j>> : 1 <= i /\ i <= j /\ j <= Len(s) }

\* Count of a value v inside a given interval of a sequence
Count(s, int, v) ==
  Cardinality({ i \in int[1] .. int[2] : s[i] = v })

\* Two sequences are permutations of each other (same multiset of elements)
Permutation(s1, s2) ==
  \A v \in Values : Count(s1, <<1, Len(s1)>>, v) = Count(s2, <<1, Len(s2)>>, v)

\* Sequence is sorted in non‑decreasing order
Sorted(s) ==
  \A i \in 1 .. Len(s)-1 : s[i] <= s[i+1]

\* Partition predicate: newSeq is a valid result of partitioning interval int
\* around pivot p in seq
Partition(s, newS, int, p) ==
  /\ \A i \in 1 .. Len(s) :
        (i < int[1] \/ i > int[2]) => newS[i] = s[i]
  /\ \A i \in int[1] .. int[2] :
        (i <= p => newS[i] <= newS[p]) /\ (i > p => newS[i] >= newS[p])
  /\ \A v \in Values :
        Count(s, int, v) = Count(newS, int, v)

\* Intervals that replace a processed interval after a split
SubIntervals(low, high, p) ==
  (IF low <= p-1 THEN { <<low, p-1>> } ELSE {}) \cup
  (IF p+1 <= high THEN { <<p+1, high>> } ELSE {})

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values) /\ seq # <<>>
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Run"

\* ----------------------------------------------------------------------
\*  Next-state relation
\* ----------------------------------------------------------------------
ProcessInterval ==
  /\ pc = "Run"
  /\ work # {}
  /\ \E int \in work :
        LET low  == int[1]
            high == int[2]
        IN
        IF low = high THEN
          /\ work' = work \ {int}
          /\ UNCHANGED <<seq, orig, pc>>
        ELSE
          /\ \E p \in low .. high :
                /\ \E newSeq \in LimitedSeq(Values) :
                      /\ Partition(seq, newSeq, int, p)
                      /\ seq' = newSeq
          /\ work' = (work \ {int}) \cup SubIntervals(low, high, p)
          /\ UNCHANGED orig
          /\ pc' = "Run"

Finish ==
  /\ pc = "Run"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
  \/ ProcessInterval
  \/ Finish
  \/ Stutter

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
vars == <<seq, orig, work, pc>>
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\*  Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq Intervals(seq)
  /\ pc \in {"Run", "Done"}

Inv ==
  Permutation(seq, orig)

PCorrect ==
  /\ pc = "Done"
  => /\ Sorted(seq)
     /\ Permutation(seq, orig)

\* ----------------------------------------------------------------------
\*  Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\*  Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* The .cfg expects the following names:
\*   CONSTANTS: Values, MaxSeqLen
\*   SPECIFICATION: Spec
\*   INVARIANTS: PCorrect, TypeOK, Inv
\*   PROPERTIES: Termination
\*   Operator: LimitedSeq (defined above)
\* ----------------------------------------------------------------------
====
---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\*--------------------------------------------------------------------
\* Types and helper operators
\*--------------------------------------------------------------------
LimitedSeq(V) == { s \in Seq(V) : Len(s) <= MaxSeqLen }

Domain(s) == 1 .. Len(s)

Count(v, s) == Cardinality({ k \in Domain(s) : s[k] = v })

Permutation(s1, s2) ==
  /\ Len(s1) = Len(s2)
  /\ \A v \in Values : Count(v, s1) = Count(v, s2)

Sorted(s) ==
  /\ Len(s) = 0 \/ Len(s) = 1
     \/ \A i \in 1 .. Len(s)-1 : s[i] <= s[i+1]

Interval(i, j) == <<i, j>>

AllIntervals(s) == { Interval(i, j) : i \in 1 .. Len(s), j \in i .. Len(s) }

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values)
  /\ Len(seq) >= 1
  /\ orig = seq
  /\ work = { Interval(1, Len(seq)) }
  /\ pc = "Loop"

\*--------------------------------------------------------------------
\* Partition abstraction
\*--------------------------------------------------------------------
UnchangedOutside(s, s2, i, j) ==
  \A k \in Domain(s) \ (i .. j) : s2[k] = s[k]

PartitionProperty(s2, i, j, p) ==
  /\ \A k \in i .. p   : s2[k] <= s2[p]
  /\ \A k \in p+1 .. j : s2[k] >= s2[p]

PartitionResult(s, s2, i, j, p) ==
  /\ Len(s2) = Len(s)
  /\ UnchangedOutside(s, s2, i, j)
  /\ PartitionProperty(s2, i, j, p)
  /\ \A v \in Values :
        Count(v, { k \in i .. j : s[k] }) =
        Count(v, { k \in i .. j : s2[k] })

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E int \in work :
          LET i == int[1] IN
          LET j == int[2] IN
          /\ i <= j
          /\ IF i = j THEN
               /\ work' = work \ {int}
               /\ seq'   = seq
               /\ orig'  = orig
               /\ pc'    = "Loop"
             ELSE
               (* non‑singleton interval *)
               /\ \E p \in i .. j :
                    /\ \E s2 \in LimitedSeq(Values) :
                         /\ PartitionResult(seq, s2, i, j, p)
                         /\ seq' = s2
                         /\ orig' = orig
                         /\ pc'   = "Loop"
                         /\ LET low  == IF i <= p-1 THEN { Interval(i, p-1) } ELSE {}
                            IN
                            LET high == IF p+1 <= j THEN { Interval(p+1, j) } ELSE {}
                            IN
                            work' = (work \ {int}) \cup low \cup high
          )
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED vars

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\*--------------------------------------------------------------------
\* Invariant
\*--------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(orig) = Len(seq)
  /\ work \subseteq AllIntervals(seq)
  /\ pc \in {"Loop", "Done"}

Inv ==
  /\ TypeOK
  /\ Permutation(orig, seq)

\*--------------------------------------------------------------------
\* Partial correctness when terminated
\*--------------------------------------------------------------------
PCorrect ==
  pc = "Done" => (Sorted(seq) /\ Permutation(orig, seq))

\*--------------------------------------------------------------------
\* Liveness property (termination)
\*--------------------------------------------------------------------
Termination == []<>(pc = "Done")

\*--------------------------------------------------------------------
\* The identifiers required by the .cfg file
\*--------------------------------------------------------------------
\* The .cfg expects the following names:
\*   SPECIFICATION  == Spec
\*   INVARIANTS     == PCorrect, TypeOK, Inv
\*   PROPERTIES     == Termination
\*   CONSTANTS      == Values, MaxSeqLen
\*   Operators      == LimitedSeq (already defined)
\*--------------------------------------------------------------------
====
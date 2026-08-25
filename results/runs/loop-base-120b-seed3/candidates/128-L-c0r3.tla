---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* LimitedSeq replaces Seq from Sequences with a finite version.
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Interval == [low : Nat, high : Nat]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, origSeq, workSet, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Count(s, v) == Cardinality({ k \in 1..Len(s) : s[k] = v })

IsPermutation(s1, s2) ==
  /\ Len(s1) = Len(s2)
  /\ \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

Partition(old, intv, piv, new) ==
  /\ Len(new) = Len(old)
  /\ \A k \in 1..Len(old) :
        IF (k < intv.low) \/ (k > intv.high) THEN new[k] = old[k] ELSE TRUE
  /\ \A k1 \in intv.low..piv : \A k2 \in (piv+1)..intv.high :
        new[k1] <= new[k2]
  /\ IsPermutation(old, new)

\* ----------------------------------------------------------------------
\* Type correctness
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ origSeq = seq
  /\ workSet \subseteq { i \in Interval :
                         1 <= i.low /\ i.low <= i.high /\ i.high <= Len(seq) }
  /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ origSeq = seq
  /\ workSet = { [low |-> 1, high |-> Len(seq)] }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Loop"
     /\ workSet # {}
     /\ \E intv \in workSet :
          /\ IF intv.low = intv.high
                THEN /\ workSet' = workSet \ {intv}
                     /\ seq' = seq
                ELSE /\ \E piv \in intv.low..intv.high :
                       \E newSeq \in LimitedSeq(Values) :
                         /\ Partition(seq, intv, piv, newSeq)
                         /\ workSet' = (workSet \ {intv}) \cup
                                        {[low |-> intv.low, high |-> piv],
                                         [low |-> piv+1, high |-> intv.high]}
                         /\ seq' = newSeq
          /\ pc' = "Loop"
          /\ UNCHANGED <<origSeq>>
  \/ /\ pc = "Loop"
     /\ workSet = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, origSeq, workSet>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, origSeq, workSet, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, origSeq, workSet, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
Inv == TypeOK

PCorrect ==
  pc = "Done" => /\ IsPermutation(seq, origSeq) /\ Sorted(seq)

\* ----------------------------------------------------------------------
\* Property: termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* (already defined with the exact names)
====
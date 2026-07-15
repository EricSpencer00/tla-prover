---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen, Seq

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Idx == 1 .. MaxSeqLen

\* The set of all non‑empty sequences of length at most MaxSeqLen drawn from Values
AllSeqs == { s \in Seq(Values) : Len(s) > 0 /\ Len(s) <= MaxSeqLen }

\* An interval is a pair <<low, high>> with 1 ≤ low ≤ high ≤ Len(seq)
Interval == [low : Nat, high : Nat]

\* The set of all intervals that are valid for a given sequence length
Intervals(len) == { [low |-> l, high |-> h] : l \in 1..len, h \in l..len }

\* Permutation of a sequence: there exists a bijection on the index set that
\* reorders the elements.
Permutation(s, t) ==
  \E f \in [1..Len(s) -> 1..Len(s)] :
    /\ \A i \in 1..Len(s) : s[i] = t[f[i]]
    /\ \A i, j \in 1..Len(s) : f[i] = f[j] => i = j

\* Sortedness predicate (non‑decreasing order)
Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in AllSeqs
  /\ orig = seq
  /\ work = { [low |-> 1, high |-> Len(seq)] }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Terminate ==
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

LoopStep ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E int \in work :
        LET low  == int.low
            high == int.high
        IN
        IF low = high THEN
          /\ work' = work \ {int}
          /\ UNCHANGED <<seq, orig>>
        ELSE
          /\ \E pivot \in low..high :
                LET lower == [low |-> low, high |-> pivot - 1]
                    upper == [low |-> pivot + 1, high |-> high]
                IN
                /\ lower.low <= lower.high => lower \in Intervals(Len(seq))
                /\ upper.low <= upper.high => upper \in Intervals(Len(seq))
                /\ \E newSeq \in AllSeqs :
                      /\ Len(newSeq) = Len(seq)
                      /\ \A i \in 1..Len(seq) :
                           (i < low \/ i > high) => newSeq[i] = seq[i]
                      /\ \A i \in low..pivot :
                           \A j \in pivot+1..high :
                               newSeq[i] <= newSeq[j]
                      /\ seq' = newSeq
                /\ work' = (work \ {int}) \cup
                           (IF lower.low <= lower.high THEN {lower} ELSE {}) \cup
                           (IF upper.low <= upper.high THEN {upper} ELSE {})
          /\ pc' = "Loop"

Next ==
  \/ LoopStep
  \/ Terminate
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Type correctness
TypeOK ==
  /\ seq \in AllSeqs
  /\ orig \in AllSeqs
  /\ work \subseteq Intervals(Len(seq))
  /\ pc \in {"Loop", "Done"}

\* Partial correctness invariant (maintained throughout execution)
Inv ==
  /\ Permutation(seq, orig)
  /\ \A int \in work :
        \A i, j \in int.low .. int.high :
            i < j => seq[i] <= seq[j]

\* Full correctness when the algorithm has terminated
PCorrect ==
  /\ pc = "Done"
  /\ Sorted(seq)
  /\ Permutation(seq, orig)

\* ----------------------------------------------------------------------
\* Theorems (optional, for TLAPS)
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => []PCorrect

====
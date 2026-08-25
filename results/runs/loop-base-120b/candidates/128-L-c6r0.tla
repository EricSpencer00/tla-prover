---- MODULE Quicksort ----
EXTENDS Sequences, FiniteSets, Naturals, Integers

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\*  Finite version of Seq for model checking
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\*  Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\*  Types
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Values \subseteq Int
    /\ MaxSeqLen \in Nat
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig = seq
    /\ work \subseteq Intervals(seq)
    /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\*  Intervals (inclusive bounds) that are valid for the current sequence
\* ----------------------------------------------------------------------
Intervals(s) == { <<i, j>> : i \in Nat /\ j \in Nat /\ i <= j /\ j <= Len(s) }

\* ----------------------------------------------------------------------
\*  Helper definitions
\* ----------------------------------------------------------------------
Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })

IsPermutation(s, t) ==
    /\ Len(s) = Len(t)
    /\ \A v \in Values : Count(s, v) = Count(t, v)

Sorted(s) ==
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* ----------------------------------------------------------------------
\*  Partition operator (nondeterministic set of possible outcomes)
\* ----------------------------------------------------------------------
Partition(old, low, high, piv) ==
    { new \in LimitedSeq(Values) :
        /\ Len(new) = Len(old)
        /\ \A k \in 1..Len(old) :
               (k < low \/ k > high) => new[k] = old[k]
        /\ \A i \in low..piv, j \in piv+1..high : new[i] <= new[j]
        /\ IsPermutation(old, new) }

\* ----------------------------------------------------------------------
\*  Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\* ----------------------------------------------------------------------
\*  Main action (one iteration of the sorting loop)
\* ----------------------------------------------------------------------
SortStep ==
    /\ pc = "Loop"
    /\ work # {}
    /\ \E int \in work :
          LET low  == int[1]
              high == int[2] IN
          IF low = high THEN
              /\ work' = work \ {int}
              /\ seq'  = seq
          ELSE
              /\ \E piv \in low..high :
                    LET lowerInt == <<low, piv-1>>
                        upperInt == <<piv+1, high>> IN
                    /\ \A i \in {lowerInt, upperInt} :
                         (i[1] <= i[2]) => TRUE   \* keep only non‑empty intervals
                    /\ newSeq \in Partition(seq, low, high, piv)
                    /\ seq'  = newSeq
                    /\ work' = (work \ {int})
                               \cup (IF low <= piv-1 THEN {lowerInt} ELSE {})
                               \cup (IF piv+1 <= high THEN {upperInt} ELSE {})
          /\ pc' = "Loop"

\* ----------------------------------------------------------------------
\*  Termination step
\* ----------------------------------------------------------------------
DoneStep ==
    /\ pc = "Loop"
    /\ work = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<seq, orig, work>>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
    SortStep \/ DoneStep \/ Stutter

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\*  Invariant that must hold in every reachable state
\* ----------------------------------------------------------------------
Inv == TypeOK

\* ----------------------------------------------------------------------
\*  Partial‑correctness property (holds when algorithm terminates)
\* ----------------------------------------------------------------------
PCorrect ==
    pc = "Done" => (Sorted(seq) /\ IsPermutation(seq, orig))

\* ----------------------------------------------------------------------
\*  Termination property
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====================
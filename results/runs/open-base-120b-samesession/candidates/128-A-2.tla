---- MODULE Quicksort ----
EXTENDS Sequences, Naturals, FiniteSets

\*-----------------------------------------------------------------------
\* Constants
\*-----------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\*-----------------------------------------------------------------------
\* Helper definitions
\*-----------------------------------------------------------------------

\* Intervals are represented as a two‑element tuple <<low,high>> with low ≤ high.
INTERVAL == <<i, j>> \in Nat \X Nat

INTERVALS == { <<i, j>> \in Nat \X Nat : i <= j }

\* A finite version of the standard Seq operator.
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* Count the occurrences of a value v in a sequence s over an index set I.
Count(s, I, v) == Cardinality({ i \in I : s[i] = v })

\* Two sequences are permutations of each other (multiset equality).
Permutes(s, t) ==
    /\ Len(s) = Len(t)
    /\ \A v \in Values : Count(s, 1..Len(s), v) = Count(t, 1..Len(t), v)

\* Sortedness predicate (non‑decreasing order).
Sorted(s) ==
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\*-----------------------------------------------------------------------
\* Variables
\*-----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\*-----------------------------------------------------------------------
\* Initialization
\*-----------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\*-----------------------------------------------------------------------
\* Partition step (nondeterministic abstract partition)
\*-----------------------------------------------------------------------
Partition(seq, int, p) ==
    LET low  == int[1]
        high == int[2]
        I    == low .. high
        Jlow == low .. p
        Jhi  == (p+1) .. high
        NewSeq == 
            { s \in LimitedSeq(Values) :
                /\ Len(s) = Len(seq)
                /\ \A i \in 1..Len(seq) :
                     (i \notin I) => s[i] = seq[i]
                /\ \A i \in Jlow, j \in Jhi : s[i] <= s[j]
                /\ Permutes( s[I], seq[I] )
            }
    IN  NewSeq

\*-----------------------------------------------------------------------
\* Next-state relation
\*-----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Loop"
       /\ work # {}
       /\ \E int \in work :
            /\ LET low  == int[1]
               high == int[2]
            IN
               /\ IF low = high
                  THEN
                     /\ work' = work \ {int}
                     /\ UNCHANGED <<seq, orig, pc>>
                  ELSE
                     /\ \E p \in low..high :
                           /\ seq' \in Partition(seq, int, p)
                           /\ work' = (work \ {int})
                                      \cup (IF low <= p-1 THEN {<<low, p-1>>} ELSE {})
                                      \cup (IF p+1 <= high THEN {<<p+1, high>>} ELSE {})
                           /\ UNCHANGED orig
                           /\ pc' = "Loop"
               )
    \/ /\ pc = "Loop"
       /\ work = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<seq, orig, work>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<seq, orig, work, pc>>

\*-----------------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\*-----------------------------------------------------------------------
\* Type correctness invariant
\*-----------------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ work \subseteq INTERVALS
    /\ pc \in {"Loop", "Done"}

\*-----------------------------------------------------------------------
\* General invariant (preserves permutation)
\*-----------------------------------------------------------------------
Inv == /\ TypeOK
       /\ Permutes(seq, orig)

\*-----------------------------------------------------------------------
\* Partial correctness when the algorithm terminates
\*-----------------------------------------------------------------------
PCorrect ==
    /\ pc = "Done"
    /\ Sorted(seq)
    /\ Permutes(seq, orig)

\*-----------------------------------------------------------------------
\* Liveness property (termination)
\*-----------------------------------------------------------------------
Termination == []<>(pc = "Done")

\*-----------------------------------------------------------------------
\* The set of invariants and properties required by the .cfg file
\*-----------------------------------------------------------------------
INVARIANTS == TypeOK, Inv, PCorrect
PROPERTIES == Termination

====
---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

\*-----------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\*-----------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\*-----------------------------------------------------------------
\* A finite version of Seq for model checking
\*-----------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\*-----------------------------------------------------------------
\* State variables
\*-----------------------------------------------------------------
VARIABLES seq, orig, work, pc

\*-----------------------------------------------------------------
\* Helper definitions
\*-----------------------------------------------------------------
Idx == 1..Len(seq)

Interval == [low : Nat, high : Nat]

\* an interval is well‑formed if it lies inside the current sequence
WellFormedInterval(i) == 
    /\ i.low \in Idx
    /\ i.high \in Idx
    /\ i.low <= i.high

\* set of all well‑formed intervals for the current sequence
AllIntervals == { i \in Interval : WellFormedInterval(i) }

\* permutation predicate (multiset equality)
Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })
Permutes(s1, s2) == 
    /\ Len(s1) = Len(s2)
    /\ \A v \in Values : Count(s1, v) = Count(s2, v)

\* sortedness predicate (non‑decreasing order)
Sorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init == 
    /\ seq \in LimitedSeq(Values) 
    /\ Len(seq) >= 1                     \* non‑empty sequence
    /\ orig = seq
    /\ work = { [low |-> 1, high |-> Len(seq)] }  \* whole array
    /\ pc = "Loop"

\*-----------------------------------------------------------------
\* Partition step (abstract)
\*-----------------------------------------------------------------
Partition(seq, w, p) == 
    \E newSeq \in LimitedSeq(Values) :
        /\ Len(newSeq) = Len(seq)
        /\ \A i \in Idx :
              (i < w.low \/ i > w.high) => newSeq[i] = seq[i]
        /\ \A i \in w.low..p :
              \A j \in p+1..w.high : newSeq[i] <= newSeq[j]
        /\ Permutes(seq, newSeq)

\*-----------------------------------------------------------------
\* The main transition relation
\*-----------------------------------------------------------------
Next == 
    \/ /\ pc = "Loop"
       /\ work # {}
       /\ \E w \in work :
            /\ WellFormedInterval(w)
            /\ IF w.low = w.high
               THEN /\ work' = work \ {w}
                    /\ UNCHANGED <<seq, orig, pc>>
               ELSE 
                 \E p \in w.low..w.high :
                    /\ Partition(seq, w, p)
                    /\ LET lower == [low |-> w.low, high |-> p-1]
                           upper == [low |-> p+1, high |-> w.high] 
                       IN 
                       /\ work' = (work \ {w}) 
                                   \cup (IF lower.low <= lower.high THEN {lower} ELSE {}) 
                                   \cup (IF upper.low <= upper.high THEN {upper} ELSE {})
                    /\ seq' \in LimitedSeq(Values) \* the new sequence chosen by Partition
                    /\ seq' \in {newSeq : Partition(seq, w, p)}   \* pick one satisfying the predicate
                    /\ orig' = orig
                    /\ pc' = "Loop"
    \/ /\ pc = "Loop"
       /\ work = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<seq, orig, work>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<seq, orig, work, pc>>

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\*-----------------------------------------------------------------
\* Type correctness invariant
\*-----------------------------------------------------------------
TypeOK == 
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ work \subseteq AllIntervals
    /\ pc \in {"Loop", "Done"}

\*-----------------------------------------------------------------
\* Permutation invariant (orig is always a permutation of current seq)
\*-----------------------------------------------------------------
Inv == TypeOK /\ Permutes(orig, seq)

\*-----------------------------------------------------------------
\* Partial‑correctness invariant (holds when algorithm terminates)
\*-----------------------------------------------------------------
PCorrect == 
    /\ pc = "Done"
    /\ Sorted(seq)
    /\ Permutes(orig, seq)

\*-----------------------------------------------------------------
\* Liveness property: termination
\*-----------------------------------------------------------------
Termination == <> (pc = "Done")

\*-----------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\*-----------------------------------------------------------------
\* SPECIFICATION formula
SPEC == Spec

\* INVARIANTS
PCorrect == PCorrect
TypeOK   == TypeOK
Inv      == Inv

\* PROPERTIES
Termination == Termination

====
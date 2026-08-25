---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* A finite version of Seq, used for model checking.
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Count of a value v in a sequence s
Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })

\* Two sequences are permutations of each other (same multiset of values)
IsPermutation(s, t) ==
    /\ Len(s) = Len(t)
    /\ \A v \in Values : Count(s, v) = Count(t, v)

\* The sequence s is sorted in non‑decreasing order
Sorted(s) ==
    (Len(s) = 0) \/ (Len(s) = 1) \/
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Predicate describing a legal partition step
Partition(old, low, high, p, new) ==
    /\ Len(old) = Len(new)
    /\ \A i \in 1..Len(old) :
          (i < low \/ i > high) => new[i] = old[i]
    /\ \A i \in low..p :
          \A j \in p+1..high : new[i] <= new[j]
    /\ IsPermutation(old, new)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Main transition (one iteration of the quicksort loop)
\* ----------------------------------------------------------------------
Main ==
    /\ pc = "Loop"
    /\ IF work = {} THEN
          /\ pc' = "Done"
          /\ UNCHANGED <<seq, orig, work>>
       ELSE
          \E int \in work :
            LET low  == int[1] IN
            LET high == int[2] IN
            IF low = high THEN
               /\ work' = work \ {int}
               /\ UNCHANGED <<seq, orig>>
               /\ pc' = "Loop"
            ELSE
               \E p \in low..high :
                 \E newSeq :
                   /\ Partition(seq, low, high, p, newSeq)
                   /\ seq' = newSeq
                   /\ pc' = "Loop"
                   /\ work' = (work \ {int})
                              \cup (IF low <= p-1 THEN { <<low, p-1>> } ELSE {})
                              \cup (IF p+1 <= high THEN { <<p+1, high>> } ELSE {})
    /\ UNCHANGED orig

\* ----------------------------------------------------------------------
\* Stuttering step after termination (to avoid deadlock)
\* ----------------------------------------------------------------------
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

Next == Main \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ work \subseteq { <<low, high>> :
          /\ low \in 1..Len(seq)
          /\ high \in low..Len(seq) }
    /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Main inductive invariant
\* ----------------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ IsPermutation(orig, seq)
    /\ \A int \in work :
          LET low  == int[1] IN
          LET high == int[2] IN
          /\ 1 <= low /\ low <= high /\ high <= Len(seq)

\* ----------------------------------------------------------------------
\* Partial‑correctness property (when terminated the result is sorted)
\* ----------------------------------------------------------------------
PCorrect ==
    /\ pc = "Done" => /\ Sorted(seq) /\ IsPermutation(orig, seq)

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* The set of invariants and properties required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK /\ Inv /\ PCorrect
PROPERTIES == Termination

====
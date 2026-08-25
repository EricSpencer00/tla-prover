---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Types and helper definitions
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })

IsPermutation(s1, s2) ==
    \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(s) ==
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Interval representation as a record
INTERVAL == [lo : Nat, hi : Nat]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Values \subseteq Int
    /\ MaxSeqLen \in Nat
    /\ seq \in Seq(Values)
    /\ Len(seq) > 0
    /\ Len(seq) <= MaxSeqLen
    /\ orig = seq
    /\ work \subseteq { I \in INTERVAL :
                     I.lo <= I.hi /\ I.lo >= 1 /\ I.hi <= Len(seq) }
    /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Partition operator (nondeterministic choice of a valid partition)
\* ----------------------------------------------------------------------
Partition(s, I, p) ==
    { s2 \in Seq(Values) :
        /\ Len(s2) = Len(s)
        /\ \A i \in 1..Len(s) :
              (i < I.lo \/ i > I.hi) => s2[i] = s[i]
        /\ \A i \in I.lo..p :
              \A j \in p+1..I.hi => s2[i] <= s2[j]
        /\ IsPermutation(s, s2) }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) \ { << >> }   \* non‑empty sequence
    /\ orig = seq
    /\ work = { [lo |-> 1, hi |-> Len(seq)] }
    /\ pc = "Running"
    /\ TypeOK

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Running"
       /\ work # {}
       /\ \E I \in work :
            LET
                single == I.lo = I.hi
                pivotSet == I.lo .. I.hi
            IN
            IF single THEN
                /\ work' = work \ {I}
                /\ seq' = seq
                /\ orig' = orig
                /\ pc' = "Running"
            ELSE
                /\ \E p \in pivotSet :
                       LET
                           lower == [lo |-> I.lo, hi |-> p]
                           upper == [lo |-> p+1, hi |-> I.hi]
                       IN
                       /\ seq' \in Partition(seq, I, p)
                       /\ work' = (work \ {I}) \cup {lower, upper}
                       /\ orig' = orig
                       /\ pc' = "Running"
    \/ /\ pc = "Running"
       /\ work = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<seq, orig, work>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
PCorrect ==
    (pc = "Done") => (Sorted(seq) /\ IsPermutation(seq, orig))

Inv == TypeOK /\ IsPermutation(seq, orig)

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* The .cfg expects the following names:
\*   SPECIFICATION formula: Spec
\*   INVARIANTS: PCorrect, TypeOK, Inv
\*   PROPERTIES: Termination
\*   CONSTANTS: Values, MaxSeqLen
\*   Operator: LimitedSeq (already defined)

====
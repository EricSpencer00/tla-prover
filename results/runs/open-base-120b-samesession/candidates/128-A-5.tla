---- MODULE Quicksort ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Types and helper definitions
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* Interval is represented as a record with fields low and high (both Nat)
Interval == [low : Nat, high : Nat]

\* Occurrences of a value in a sequence
Occurs(v, s) == #{ i \in DOMAIN s : s[i] = v }

\* Permutation predicate (multiset equality)
IsPermutation(s, t) == \A v \in Values : Occurs(v, s) = Occurs(v, t)

\* Sortedness predicate (non‑decreasing order)
Sorted(s) == \A i, j \in DOMAIN s : i < j => s[i] <= s[j]

\* Partition predicate: newSeq is a valid result of partitioning
Partition(oldSeq, intv, piv, newSeq) ==
    /\ newSeq \in LimitedSeq(Values)
    /\ Len(newSeq) = Len(oldSeq)
    /\ \A i \in DOMAIN oldSeq :
          (i < intv.low \/ i > intv.high) => newSeq[i] = oldSeq[i]
    /\ \A i \in intv.low .. piv :
          \A j \in piv+1 .. intv.high :
              newSeq[i] <= newSeq[j]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) >= 1
    /\ orig = seq
    /\ work = { [low |-> 1, high |-> Len(seq)] }
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Run"
       /\ work # {}
       /\ \E I \in work :
            LET low  == I.low
                high == I.high
            IN
            IF low = high THEN
                /\ work' = work \ {I}
                /\ seq'  = seq
                /\ orig' = orig
                /\ pc'   = "Run"
            ELSE
                /\ \E piv \in low .. high :
                       \E newSeq \in LimitedSeq(Values) :
                           Partition(seq, I, piv, newSeq)
                /\ seq'  = newSeq
                /\ orig' = orig
                /\ work' = (work \ {I}) \cup
                          (IF low <= piv-1 THEN
                               { [low |-> low,  high |-> piv-1] }
                           ELSE {}) \cup
                          (IF piv+1 <= high THEN
                               { [low |-> piv+1, high |-> high] }
                           ELSE {})
                /\ pc'   = "Run"
    \/ /\ pc = "Run"
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
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ work \subseteq { I \in Interval :
                         I.low <= I.high /\ I.high <= Len(seq) }
    /\ pc \in {"Run", "Done"}

Inv == TypeOK
       /\ \A I \in work :
            I.low <= I.high /\ I.high <= Len(seq)

PCorrect ==
    (work = {} => Sorted(seq) /\ IsPermutation(seq, orig))

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == []<>(work = {})

====
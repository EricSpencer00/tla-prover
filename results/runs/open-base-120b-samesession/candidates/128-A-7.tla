---- MODULE Quicksort ----
EXTENDS Sequences, FiniteSets, Integers, Naturals

\* ----------------------------------------------------------------------
\* Constants required by the .cfg file
\* ----------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* A finite version of Seq, limited by MaxSeqLen
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == <<seq, orig, work, pc>>

\* an interval is a record with lower and upper inclusive bounds
Interval == [lo : Nat, hi : Nat]

IntervalIndices(i) == i.lo .. i.hi

IntervalSize(i) == i.hi - i.lo + 1

\* sortedness of a sequence (non‑decreasing order)
Sorted(s) == 
    /\ Len(s) = 0 \/ Len(s) = 1
    \/ \A i \in 1 .. Len(s)-1 : s[i] <= s[i+1]

\* count of a value v in a sequence s
Count(s, v) == Cardinality({ i \in 1 .. Len(s) : s[i] = v })

\* permutation equivalence (multiset equality)
IsPermutation(s1, s2) == 
    /\ Len(s1) = Len(s2)
    /\ \A v \in Values : Count(s1, v) = Count(s2, v)

\* restriction of a sequence to an index set I (produces a new sequence)
Restrict(s, I) == 
    [i \in 1..Cardinality(I) |-> s[SeqEnum(I)[i]]]

\* multiset equality of two restricted parts
IntervalMultisetEqual(s, t, intv) ==
    \A v \in Values :
        Count(Restrict(s, IntervalIndices(intv)), v) =
        Count(Restrict(t, IntervalIndices(intv)), v)

\* partition operator: all sequences that could result from a correct
\* partition of interval intv around pivot p.
Partition(s, intv, p) ==
    { ns \in LimitedSeq(Values) :
        /\ Len(ns) = Len(s)
        /\ \A j \in 1 .. Len(s) :
            IF j \notin IntervalIndices(intv) THEN ns[j] = s[j] ELSE TRUE
        /\ \A j \in IntervalIndices(intv) :
            IF j <= p THEN ns[j] <= ns[p] ELSE ns[j] >= ns[p]
        /\ IntervalMultisetEqual(s, ns, intv)
    }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig = seq
    /\ work = { [lo |-> 1, hi |-> Len(seq)] }
    /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Loop"
       /\ work # {}
       /\ \E intv \in work :
            LET sz == IntervalSize(intv) IN
            IF sz = 1 THEN
                /\ work' = work \ {intv}
                /\ UNCHANGED <<seq, orig, pc>>
            ELSE
                /\ \E p \in IntervalIndices(intv) :
                       LET ns == CHOOSE ns \in Partition(seq, intv, p) IN
                       /\ seq' = ns
                /\ work' =
                     (work \ {intv}) \cup
                     (IF p > intv.lo THEN { [lo |-> intv.lo, hi |-> p-1] } ELSE {}) \cup
                     (IF p < intv.hi THEN { [lo |-> p+1, hi |-> intv.hi] } ELSE {})
                /\ UNCHANGED orig
                /\ UNCHANGED pc
    \/ /\ pc = "Loop"
       /\ work = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<seq, orig, work>>
    \/ /\ pc = "Done"
       /\ UNCHANGED vars

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ work \subseteq { i \in Interval : 
                         i.lo \in 1 .. Len(seq) /\ 
                         i.hi \in i.lo .. Len(seq) }
    /\ pc \in {"Loop", "Done"}

PCorrect ==
    /\ pc = "Done"
    => /\ Sorted(seq)
       /\ IsPermutation(seq, orig)

Inv == TypeOK /\ (pc = "Done" => Sorted(seq) /\ IsPermutation(seq, orig))

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* The identifiers required by the configuration file
\* ----------------------------------------------------------------------
\* SPECIFICATION formula
SPECIFICATION == Spec

\* INVARIANTS
INVARIANTS == <<PCorrect, TypeOK, Inv>>

\* PROPERTIES
PROPERTIES == <<Termination>>

====
---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Finite version of Seq, used for model checking.
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Intervals (contiguous ranges of indices)
\* ----------------------------------------------------------------------
Interval == [lo : Nat, hi : Nat]

InInterval(i, I) == I.lo <= i /\ i <= I.hi

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
Sorted(s) ==
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

Permutation(s1, s2) ==
    \A v \in Values :
        Cardinality({ i \in 1..Len(s1) : s1[i] = v })
        =
        Cardinality({ i \in 1..Len(s2) : s2[i] = v })

\* ----------------------------------------------------------------------
\* Partition operator: nondeterministically picks any sequence that could
\* result from a correct partition of the interval I around pivot p.
\* ----------------------------------------------------------------------
Partition(s, I, p) ==
    { s2 \in LimitedSeq(Values) :
        /\ Len(s2) = Len(s)
        /\ \A i \in 1..Len(s) :
              (i \notin I.lo..I.hi) => s2[i] = s[i]
        /\ \A i \in I.lo..p, j \in p+1..I.hi : s2[i] <= s2[j]
        /\ Permutation(s2, s) }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig = seq
    /\ work = { [lo |-> 1, hi |-> Len(seq)] }
    /\ pc   = "Loop"

\* ----------------------------------------------------------------------
\* One iteration of the quicksort algorithm
\* ----------------------------------------------------------------------
LoopStep ==
    /\ pc = "Loop"
    /\ IF #work > 0 THEN
          \E I \in work :
            IF I.lo = I.hi THEN
               /\ work' = work \ {I}
               /\ UNCHANGED <<seq, orig>>
               /\ pc'   = "Loop"
            ELSE
               \E p \in I.lo..I.hi :
                 /\ seq' \in Partition(seq, I, p)
                 /\ LET lower == [lo |-> I.lo, hi |-> p],
                        upper == [lo |-> p+1, hi |-> I.hi] IN
                        work' = (work \ {I})
                                 \cup (IF lower.lo <= lower.hi THEN {lower} ELSE {})
                                 \cup (IF upper.lo <= upper.hi THEN {upper} ELSE {})
                 /\ orig' = orig
                 /\ pc'   = "Loop"
       ELSE
          /\ work = {}
          /\ pc' = "Done"
          /\ UNCHANGED <<seq, orig>>

\* ----------------------------------------------------------------------
\* Stuttering step after termination to avoid deadlock
\* ----------------------------------------------------------------------
DoneStutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
    LoopStep \/ DoneStutter

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
    /\ Len(seq) = Len(orig)
    /\ work \subseteq { I \in Interval : I.lo >= 1 /\ I.hi <= Len(seq) /\ I.lo <= I.hi }
    /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Main invariant (permutation preservation and partial sortedness)
\* ----------------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ Permutation(seq, orig)
    /\ \A I \in work :
         \A i \in I.lo..I.hi :
           \A j \in I.lo..I.hi :
              i < j => seq[i] <= seq[j]

\* ----------------------------------------------------------------------
\* Partial‑correctness condition: when the algorithm terminates the
\* sequence is sorted and a permutation of the original input.
\* ----------------------------------------------------------------------
PCorrect ==
    /\ pc = "Done"
    /\ Sorted(seq)
    /\ Permutation(seq, orig)

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* Specification formula
Spec

\* Invariants
PCorrect
TypeOK
Inv

\* Properties
Termination
====
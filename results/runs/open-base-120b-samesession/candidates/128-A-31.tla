---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* A finite version of Seq, bounded by MaxSeqLen (used in the .cfg)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
Indices(s) == 1 .. Len(s)

Interval == [lo : Nat, hi : Nat]

IntervalIndices(i) == i.lo .. i.hi

IsSingleton(i) == i.lo = i.hi

Count(s, v, I) == Cardinality({ j \in I : s[j] = v })

Permutation(s1, s2, I) == 
    /\ I \subseteq Indices(s1)
    /\ I \subseteq Indices(s2)
    /\ \A v \in Values : Count(s1, v, I) = Count(s2, v, I)

Sorted(s) == \A i, j \in Indices(s) : i < j => s[i] <= s[j]

PartitionPredicate(s, i, p, sNew) ==
    /\ sNew \in LimitedSeq(Values)
    /\ \A k \in Indices(s) : 
          (k \notin IntervalIndices(i) => sNew[k] = s[k])
    /\ Permutation(s, sNew, IntervalIndices(i))
    /\ \A k, l \in IntervalIndices(i) :
          (k <= p /\ p < l) => sNew[k] <= sNew[l]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ seq \in LimitedSeq(Values)
    /\ Len(seq) > 0
    /\ orig = seq
    /\ work = { [lo |-> 1, hi |-> Len(seq)] }
    /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* The main step
Step ==
    /\ pc = "Loop"
    /\ work # {}
    /\ \E i \in work :
        LET
            newWork ==
                IF IsSingleton(i) THEN
                    work \ {i}
                ELSE
                    (* choose a pivot and partition *)
                    CHOOSE p \in i.lo .. i.hi :
                        \E sNew \in LimitedSeq(Values) :
                            PartitionPredicate(seq, i, p, sNew)
                    LET
                        lower == [lo |-> i.lo, hi |-> p]
                        upper == [lo |-> p + 1, hi |-> i.hi]
                        work' == (work \ {i}) \cup {lower, upper}
                    IN
                        work' 
        IN
            /\ IF IsSingleton(i) THEN
                    /\ seq' = seq
                    /\ work' = work \ {i}
               ELSE
                    /\ \E p \in i.lo .. i.hi :
                         \E sNew \in LimitedSeq(Values) :
                            /\ PartitionPredicate(seq, i, p, sNew)
                            /\ seq' = sNew
                    /\ work' = (work \ {i}) \cup { [lo|-> i.lo, hi|-> p],
                                                [lo|-> p+1, hi|-> i.hi] }
            /\ pc' = IF work' = {} THEN "Done" ELSE "Loop"

\* ----------------------------------------------------------------------
\* Stuttering after termination
DoneStutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

Next == Step \/ DoneStutter

\* ----------------------------------------------------------------------
\* Specification
vars == <<seq, orig, work, pc>>
Spec == Init /\ [] [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ work \subseteq { [lo |-> l, hi |-> h] : l \in Nat, h \in Nat, l <= h,
                        l \in Indices(seq), h \in Indices(seq) }
    /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Program‑counter correctness invariant
PCorrect == (pc = "Loop") <=> (work # {})

\* ----------------------------------------------------------------------
\* Main inductive invariant (permutation preservation)
Inv ==
    /\ Permutation(seq, orig, Indices(seq))

\* ----------------------------------------------------------------------
\* Liveness property: termination
Termination == <> (work = {})

====
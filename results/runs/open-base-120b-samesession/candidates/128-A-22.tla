---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\*-----------------------------------------------------------------
\* Constants
\*-----------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\*-----------------------------------------------------------------
\* Helper definitions
\*-----------------------------------------------------------------
\* Finite version of Seq, limited by MaxSeqLen
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* Interval representation as a two‑element tuple <<lo,hi>>
Interval == <<lo, hi>> \in (Nat \X Nat)

\* Set of all well‑formed intervals for a sequence of length n
Intervals(n) == { <<lo, hi>> \in (1..n) \X (1..n) : lo <= hi }

\* Count of value v in a sequence s
Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })

\* Permutation predicate
Permutes(s1, s2) == 
    /\ Len(s1) = Len(s2)
    /\ \A v \in Values : Count(s1, v) = Count(s2, v)

\* Sortedness predicate (non‑decreasing order)
Sorted(s) == 
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Partition operator: all sequences that could result from a valid
\* partition of interval I around pivot p.
Partition(seq, I, p) == 
    { newSeq \in LimitedSeq(Values) :
        /\ Len(newSeq) = Len(seq)
        /\ \A i \in 1..Len(seq) : 
            (i #<< I.lo, I.hi >>) => newSeq[i] = seq[i]
        /\ \A i \in I.lo..p :
            \A j \in p+1..I.hi :
                newSeq[i] <= newSeq[j]
        /\ Permutes( 
                [i \in I.lo..I.hi |-> newSeq[i]],
                [i \in I.lo..I.hi |-> seq[i]] )
    }

\* Helper to test membership of an index in an interval
\* (used in the definition of Partition)
\* i #<< lo, hi >> is true iff i \in lo..hi
i #<< lo, hi >> == i \in lo..hi

\*-----------------------------------------------------------------
\* Variables
\*-----------------------------------------------------------------
VARIABLES seq, orig, work, pc

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\*-----------------------------------------------------------------
\* Next-state relation
\*-----------------------------------------------------------------
Next ==
    \/ /\ pc = "Loop"
       /\ work # {}
       /\ \E I \in work :
            LET lo == I[1] IN
            LET hi == I[2] IN
            IF lo = hi THEN
                /\ work' = work \ {I}
                /\ UNCHANGED <<seq, orig, pc>>
            ELSE
                /\ \E p \in lo..hi :
                    /\ newSeq \in Partition(seq, I, p)
                    /\ seq' = newSeq
                    /\ pc' = "Loop"
                    /\ work' = 
                        (work \ {I}) \cup 
                        {<<lo, p>>, <<p+1, hi>>} 
                        \ {<<l, h>> \in {<<lo, p>>, <<p+1, hi>>} : l > h}
                    /\ UNCHANGED orig
            END
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
\* Invariants
\*-----------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ Len(seq) = Len(orig)
    /\ work \subseteq Intervals(Len(seq))

Inv ==
    /\ TypeOK
    /\ Permutes(seq, orig)

PCorrect ==
    /\ pc = "Done"
    => /\ Sorted(seq)
       /\ Permutes(seq, orig)

\*-----------------------------------------------------------------
\* Property (termination)
\*-----------------------------------------------------------------
Termination == <> (pc = "Done")

====
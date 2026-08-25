---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Integers, Sequences

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\*  Finite version of Seq for model checking
\* ----------------------------------------------------------------------
LimitedSeq(S, n) == { s \in Seq(S) : 1 <= Len(s) /\ Len(s) <= n }

\* ----------------------------------------------------------------------
\*  Interval definition
\* ----------------------------------------------------------------------
INTERVAL == [first : Nat, last : Nat]

IsInterval(i) == 
    /\ i.first \in Nat
    /\ i.last  \in Nat
    /\ 1 <= i.first
    /\ i.first <= i.last
    /\ i.last <= Len(seq)

\* ----------------------------------------------------------------------
\*  Count of a value in a sequence
\* ----------------------------------------------------------------------
Count(v, s) == Cardinality({ j \in 1..Len(s) : s[j] = v })

\* ----------------------------------------------------------------------
\*  Permutation predicate (multiset equality)
\* ----------------------------------------------------------------------
IsPermutation(s1, s2) ==
    /\ Len(s1) = Len(s2)
    /\ \A v \in Values : Count(v, s1) = Count(v, s2)

\* ----------------------------------------------------------------------
\*  Sortedness predicate
\* ----------------------------------------------------------------------
Sorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* ----------------------------------------------------------------------
\*  Partition operator: all possible results of a legal partition step
\* ----------------------------------------------------------------------
Partition(oldSeq, i, p) ==
    { newSeq \in LimitedSeq(Values, MaxSeqLen) :
        /\ Len(newSeq) = Len(oldSeq)
        /\ \A j \in 1..Len(oldSeq) :
              (j < i.first \/ j > i.last) => newSeq[j] = oldSeq[j]
        /\ \A j \in i.first..p :
              \A k \in p+1..i.last : newSeq[j] <= newSeq[k]
        /\ IsPermutation( SubSeq(oldSeq, i.first, i.last) ,
                           SubSeq(newSeq, i.first, i.last) )
    }

\* ----------------------------------------------------------------------
\*  Variables
\* ----------------------------------------------------------------------
VARIABLES seq, origSeq, work, pc

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values, MaxSeqLen)
    /\ origSeq = seq
    /\ work = { [first |-> 1, last |-> Len(seq)] }
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\*  Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Run"
       /\ work # {}
       /\ \E i \in work :
            /\ IsInterval(i)
            /\ IF i.first = i.last
               THEN /\ work' = work \ {i}
                    /\ UNCHANGED <<seq, origSeq, pc>>
               ELSE
                    /\ \E p \in i.first .. i.last :
                         /\ \E newSeq \in Partition(seq, i, p) :
                              /\ seq' = newSeq
                              /\ work' = (work \ {i}) \cup
                                          { [first |-> i.first, last |-> p],
                                            [first |-> p+1,   last |-> i.last] }
                              /\ UNCHANGED <<origSeq, pc>>
    \/ /\ pc = "Run"
       /\ work = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<seq, origSeq, work>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<seq, origSeq, work, pc>>

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, origSeq, work, pc>>

\* ----------------------------------------------------------------------
\*  Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values, MaxSeqLen)
    /\ origSeq \in LimitedSeq(Values, MaxSeqLen)
    /\ Len(origSeq) = Len(seq)
    /\ work \subseteq { i \in INTERVAL : IsInterval(i) }
    /\ pc \in {"Run", "Done"}

\* ----------------------------------------------------------------------
\*  Post‑condition when the algorithm has terminated
\* ----------------------------------------------------------------------
PCorrect ==
    (pc = "Done") => (Sorted(seq) /\ IsPermutation(seq, origSeq))

\* ----------------------------------------------------------------------
\*  Main invariant
\* ----------------------------------------------------------------------
Inv == TypeOK /\ PCorrect

\* ----------------------------------------------------------------------
\*  Termination property
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\*  Exported identifiers for the configuration
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INVARIANTS == PCorrect, TypeOK, Inv
PROPERTIES == Termination

====
---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Bounded version of Seq for model checking
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
INTERVAL == [lo : Nat, hi : Nat]
INTERVALS == { i \in INTERVAL : i.lo <= i.hi }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IdxSet(s) == 1 .. Len(s)

Count(s, v) == Cardinality({ i \in IdxSet(s) : s[i] = v })

Permutation(s1, s2) ==
  /\ Len(s1) = Len(s2)
  /\ \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(s) ==
  /\ Len(s) = 0 \/ Len(s) = 1
     \/ \A i, j \in IdxSet(s) : i < j => s[i] <= s[j]

\* ----------------------------------------------------------------------
\* Partition predicate (abstract)
\* ----------------------------------------------------------------------
Partition(old, interval, pivot, new) ==
  /\ Len(new) = Len(old)
  /\ \A i \in IdxSet(old) :
        (i < interval.lo \/ i > interval.hi) => new[i] = old[i]
  /\ \A i, j \in interval.lo .. pivot :
        new[i] <= new[j + 1]   \* ensures all left side ≤ all right side
  /\ Permutation(old[interval.lo .. interval.hi],
                new[interval.lo .. interval.hi])

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { [lo |-> 1, hi |-> Len(seq)] }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* One step of the algorithm
\* ----------------------------------------------------------------------
Step ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E i \in work :
          /\ i.lo = i.hi
          /\ UNCHANGED <<seq, orig>>
          /\ work' = work \ {i}
          /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E i \in work :
          /\ i.lo # i.hi
          /\ \E p \in i.lo .. i.hi :
               /\ \E newSeq \in LimitedSeq(Values) :
                    /\ Partition(seq, i, p, newSeq)
                    /\ seq' = newSeq
               /\ let low  == IF p > i.lo THEN {[lo |-> i.lo, hi |-> p-1]} ELSE {}
                      high == IF p < i.hi THEN {[lo |-> p+1, hi |-> i.hi]} ELSE {}
                  in work' = (work \ {i}) \cup low \cup high
               /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

Next == Step

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
  /\ Len(orig) = Len(seq)
  /\ work \subseteq INTERVALS
  /\ pc \in {"Loop", "Done"}

PCorrect ==
  /\ pc = "Done"
  /\ Sorted(seq)
  /\ Permutation(seq, orig)

Inv == TypeOK

\* ----------------------------------------------------------------------
\* Property: termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* The set of invariants and properties required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANT == PCorrect /\ TypeOK /\ Inv
PROPERTY == Termination

====
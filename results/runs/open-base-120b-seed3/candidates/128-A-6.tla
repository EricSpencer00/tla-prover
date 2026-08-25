---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Bounded sequences of values
\* ----------------------------------------------------------------------
LimitedSeq == { s \in Seq(Values) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, origSeq, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* All intervals that can appear for the current sequence length
AllIntervals == { <<i, j>> : i \in 1..Len(seq) /\ j \in i..Len(seq) }

\* Bag (multiset) of a whole sequence
Bag(s) == [v \in Values |-> 
            Cardinality({ i \in DOMAIN s : s[i] = v })]

\* Bag of a sub‑range [low .. high] of a sequence
BagRestrict(s, low, high) ==
  [v \in Values |-> 
     Cardinality({ i \in low..high : s[i] = v })]

\* Predicate that a new sequence is a valid partition of the interval
\* [low,high] around pivot p (inclusive).  Elements outside the interval are unchanged,
\* elements in the lower part are <= the pivot value, elements in the upper part are >= it,
\* and the multiset of values inside the interval is preserved.
IsPartition(old, new, int, p) ==
  LET low  == int[1] IN
  LET high == int[2] IN
  /\ Len(old) = Len(new)
  /\ \A i \in DOMAIN old :
        IF i \notin low..high THEN new[i] = old[i] ELSE TRUE
  /\ \A i \in low..p   : new[i] <= new[p]
  /\ \A i \in p+1..high: new[p] <= new[i]
  /\ BagRestrict(old, low, high) = BagRestrict(new, low, high)

\* Predicate that a sequence is sorted in non‑decreasing order
IsSorted(s) == \A i \in 1..Len(s)-1 : s[i] <= s[i+1]

\* Permutation predicate (multiset equality)
Permutation(s1, s2) == \A v \in Values : Bag(s1)[v] = Bag(s2)[v]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq
  /\ Len(seq) > 0
  /\ origSeq = seq
  /\ work = {<<1, Len(seq)>>}
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ LET int == CHOOSE I \in work : TRUE
        IN
        IF int[1] = int[2] THEN
          /\ work' = work \ {int}
          /\ UNCHANGED <<seq, origSeq, pc>>
        ELSE
          LET p == CHOOSE j \in int[1]..int[2] : TRUE
              newSeq \in { s \in LimitedSeq :
                            Len(s) = Len(seq) /\ IsPartition(seq, s, int, p) }
          IN
          /\ seq' = newSeq
          /\ work' = (work \ {int}) \cup {<<int[1], p>>, <<p+1, int[2>>}}
          /\ UNCHANGED origSeq
          /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, origSeq, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, origSeq, work, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, origSeq, work, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq
  /\ origSeq \in LimitedSeq
  /\ work \subseteq AllIntervals
  /\ pc \in {"Loop", "Done"}

Inv ==
  /\ TypeOK
  /\ Permutation(seq, origSeq)

PCorrect ==
  (pc = "Done") => /\ IsSorted(seq) /\ Permutation(seq, origSeq)

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

=============================================================================
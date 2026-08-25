---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Finite version of Seq, limited by MaxSeqLen
LimitedSeq(V) == { s \in Seq(V) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Types
INTERVAL == [lo : Nat, hi : Nat]

\* ----------------------------------------------------------------------
\* Helper definitions
Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })
IsPermutation(s, o) == 
   /\ Len(s) = Len(o)
   /\ \A v \in Values : Count(s, v) = Count(o, v)

IsSorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* ----------------------------------------------------------------------
\* Initial predicate
Init ==
   /\ seq \in LimitedSeq(Values) 
   /\ Len(seq) > 0
   /\ orig = seq
   /\ work = { [lo |-> 1, hi |-> Len(seq)] }
   /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Action: remove a singleton interval
RemoveSingleton ==
   /\ pc = "Loop"
   /\ work # {}
   /\ \E I \in work : I.lo = I.hi
   /\ LET I == CHOOSE i \in work : i.lo = i.hi IN
        /\ work' = work \ {I}
        /\ UNCHANGED <<seq, orig, pc>>

\* ----------------------------------------------------------------------
\* Action: partition a non‑singleton interval
Partition ==
   /\ pc = "Loop"
   /\ work # {}
   /\ \E I \in work : I.lo < I.hi
   /\ LET I == CHOOSE i \in work : i.lo < i.hi IN
        /\ \E p \in I.lo .. I.hi :
              LET lower == [lo |-> I.lo, hi |-> p] IN
              LET upper == [lo |-> p+1, hi |-> I.hi] IN
              /\ work' = (work \ {I}) \cup {lower, upper}
              /\ \E newSeq \in LimitedSeq(Values) :
                    /\ Len(newSeq) = Len(seq)
                    /\ \A i \in 1..Len(seq) :
                         (i \notin I.lo .. I.hi) => newSeq[i] = seq[i]
                    /\ \A i \in I.lo .. p, j \in p+1 .. I.hi :
                         newSeq[i] <= newSeq[j]
                    /\ \A i \in I.lo .. I.hi : newSeq[i] \in Values
                    /\ seq' = newSeq
              /\ UNCHANGED orig
              /\ pc' = "Loop"

\* ----------------------------------------------------------------------
\* Action: termination when work set is empty
Terminate ==
   /\ pc = "Loop"
   /\ work = {}
   /\ pc' = "Done"
   /\ UNCHANGED <<seq, orig, work>>

\* ----------------------------------------------------------------------
\* Stuttering after termination (prevents deadlock)
Stutter ==
   /\ pc = "Done"
   /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Next-state relation
Next == RemoveSingleton \/ Partition \/ Terminate \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
   /\ seq \in LimitedSeq(Values)
   /\ orig \in LimitedSeq(Values)
   /\ work \subseteq INTERVAL
   /\ \A I \in work :
        /\ I.lo \in 1..Len(seq)
        /\ I.hi \in I.lo..Len(seq)
   /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Inductive invariant (includes TypeOK and well‑formed intervals)
Inv == TypeOK

\* ----------------------------------------------------------------------
\* Partial‑correctness property: when terminated the result is sorted
\* and a permutation of the original input
PCorrect ==
   /\ pc = "Done"
   => /\ IsSorted(seq)
      /\ IsPermutation(seq, orig)

\* ----------------------------------------------------------------------
\* Liveness property: the algorithm eventually terminates
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* The set of constants is assumed to satisfy the following:
ASSUME Values \subseteq Int
ASSUME MaxSeqLen \in Nat \ {0}

====
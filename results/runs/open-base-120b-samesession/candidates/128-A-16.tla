---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Bounded version of Seq
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Interval == [lo : Nat, hi : Nat]   \* lo ≤ hi will be ensured where used

\* ----------------------------------------------------------------------
\* Helper operators
\* ----------------------------------------------------------------------
Count(s, v) == Cardinality({ i \in DOMAIN s : s[i] = v })

Permutes(s, t) == /\ Len(s) = Len(t)
                 /\ \A v \in Values : Count(s, v) = Count(t, v)

IsSorted(s) == \A i, j \in DOMAIN s : i < j => s[i] <= s[j]

Intervals(seq) == { I \in [lo : Nat, hi : Nat] :
                     I.lo \in 1..Len(seq) /\ I.hi \in I.lo..Len(seq) }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig = seq
    /\ work = { [lo |-> 1, hi |-> Len(seq)] }
    /\ pc = "Main"

\* ----------------------------------------------------------------------
\* Partition relation (nondeterministic choice of a valid partition)
\* ----------------------------------------------------------------------
Partition(oldSeq, I, p) ==
    { newSeq \in LimitedSeq(Values) :
        /\ Len(newSeq) = Len(oldSeq)
        /\ \A i \in DOMAIN oldSeq :
               (i \notin I.lo..I.hi) => newSeq[i] = oldSeq[i]
        /\ Permutes(oldSeq, newSeq)
        /\ \A i \in I.lo..p :
              \A j \in (p+1)..I.hi :
                  newSeq[i] <= newSeq[j] }

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Main"
     /\ work # {}
     /\ \E I \in work :
          /\ I.lo = I.hi
          /\ /\ work' = work \ {I}
             /\ UNCHANGED <<seq, orig, pc>>
  \/ /\ pc = "Main"
     /\ work # {}
     /\ \E I \in work :
          /\ I.lo < I.hi
          /\ \E p \in I.lo..I.hi :
                \E newSeq \in Partition(seq, I, p) :
                    /\ seq' = newSeq
                    /\ orig' = orig
                    /\ pc' = pc
                    /\ let lower == [lo |-> I.lo, hi |-> p] in
                       let upper == [lo |-> p+1, hi |-> I.hi] in
                       let newInts ==
                         { lower } \cup
                         (IF p+1 <= I.hi THEN { upper } ELSE {}) in
                       work' = (work \ {I}) \cup newInts
  \/ /\ pc = "Main"
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
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ Len(seq) = Len(orig)
    /\ work \subseteq Intervals(seq)
    /\ pc \in {"Main", "Done"}

\* ----------------------------------------------------------------------
\* General invariant (preserves permutation)
\* ----------------------------------------------------------------------
Inv == /\ TypeOK
       /\ Permutes(seq, orig)

\* ----------------------------------------------------------------------
\* Partial correctness invariant (when finished)
\* ----------------------------------------------------------------------
PCorrect == (work = {} => /\ IsSorted(seq) /\ Permutes(seq, orig))

\* ----------------------------------------------------------------------
\* Liveness property: termination
\* ----------------------------------------------------------------------
Termination == <> (work = {})

\* ----------------------------------------------------------------------
\* Theorem statements (optional, for TLAPS)
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => []PCorrect
THEOREM Spec => Termination

====
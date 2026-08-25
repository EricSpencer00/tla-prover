---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Bounded sequence operator (replaces Seq from Sequences)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Interval definition
Interval == [lo : Nat, hi : Nat]

Indices(I) == I.lo .. I.hi

\* ----------------------------------------------------------------------
\* Permutation of a subsequence (multiset equality)
PermutationOver(old, new, I) ==
  \A v \in Values :
    Cardinality({ i \in Indices(I) : old[i] = v }) =
    Cardinality({ i \in Indices(I) : new[i] = v })

\* ----------------------------------------------------------------------
\* Set of all possible partition results for a given interval and pivot
Partition(old, I, p) ==
  { new \in LimitedSeq(Values) :
      /\ Len(new) = Len(old)
      /\ \A i \in 1..Len(old) :
           (i \notin Indices(I) => new[i] = old[i])
      /\ \A i \in Indices(I) :
           i <= p => \A j \in Indices(I) :
                       j > p => new[i] <= new[j]
      /\ PermutationOver(old, new, I) }

\* ----------------------------------------------------------------------
\* Helper to add a non‑empty interval to a set
AddInterval(I) == IF I.lo <= I.hi THEN { I } ELSE {}

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ seq \in LimitedSeq(Values)
  /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { [lo |-> 1, hi |-> Len(seq)] }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Program counter correctness
PCorrect == (pc = "Done") <=> (work = {})

\* ----------------------------------------------------------------------
\* Type correctness
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ work \subseteq [lo : Nat, hi : Nat]
  /\ \A I \in work :
        /\ I.lo <= I.hi
        /\ I.lo >= 1
        /\ I.hi <= Len(seq)
  /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Main invariant (permutation of the whole sequence)
WholeInterval == [lo |-> 1, hi |-> Len(seq)]

Inv ==
  /\ PermutationOver(orig, seq, WholeInterval)

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
  \/ /\ pc = "Loop"
     /\ IF work = {} THEN
          /\ pc' = "Done"
          /\ UNCHANGED <<seq, orig, work>>
        ELSE
          \E I \in work :
            LET inds == Indices(I) IN
            IF I.lo = I.hi THEN
               /\ work' = work \ { I }
               /\ seq'  = seq
               /\ orig' = orig
               /\ pc'   = "Loop"
            ELSE
               \E p \in inds :
                 \E s' \in Partition(seq, I, p) :
                   /\ seq'  = s'
                   /\ work' = (work \ { I })
                             \cup AddInterval([lo |-> I.lo, hi |-> p-1])
                             \cup AddInterval([lo |-> p+1, hi |-> I.hi])
                   /\ orig' = orig
                   /\ pc'   = "Loop"
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Liveness property (termination)
Termination == <> (pc = "Done")

=============================================================================
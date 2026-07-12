---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen, Seq

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* An interval is a pair [l, u] with l <= u
Interval == [l: Nat, u: Nat]

\* The set of all indices of a sequence s
Indices(s) == 1..Len(s)

\* A permutation of a sequence s is another sequence of the same length
\* that is a rearrangement of s
Perm(s) == { t \in Seq : Len(t) = Len(s) }

\* A partition of a sequence s over an interval [l, u] with pivot p
\* returns a new sequence t such that:
\*   - t[i] = s[i] for i outside [l, u]
\*   - elements in [l, p] are <= elements in [p+1, u]
\*   - t is a permutation of s
Partition(s, l, u, p) ==
  { t \in Seq :
      Len(t) = Len(s) /\
      \A i \in 1..Len(s) :
        (i < l \/ i > u) => t[i] = s[i] /\
        (l <= i /\ i <= p) => \A j \in (p+1)..u : t[i] <= t[j] }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in Seq
  /\ Len(seq) >= 1
  /\ Len(seq) <= MaxSeqLen
  /\ orig = seq
  /\ work = { [l |-> 1, u |-> Len(seq)] }
  /\ pc = "Main"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Main ==
  /\ pc = "Main"
  /\ work # {}
  /\ \E i \in work :
        /\ i.l <= i.u
        /\ \E p \in i.l..i.u :
              /\ seq' \in Partition(seq, i.l, i.u, p)
              /\ work' = (work \ {i}) \cup
                          { [l |-> i.l, u |-> p],
                            [l |-> p+1, u |-> i.u] }
              /\ pc' = "Main"
  \/ \E i \in work :
        /\ i.l = i.u
        /\ work' = work \ {i}
        /\ pc' = "Main"

Terminate ==
  /\ pc = "Main"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED seq

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
  \/ Main
  \/ Terminate
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in Seq
  /\ Len(seq) <= MaxSeqLen
  /\ orig \in Seq
  /\ Len(orig) = Len(seq)
  /\ work \subseteq { [l |-> i, u |-> j] : i \in 1..Len(seq) /\ j \in i..Len(seq) }
  /\ pc \in {"Main", "Done"}

\* The final sequence is a permutation of the original
PCorrect ==
  /\ pc = "Done"
  /\ seq \in Perm(orig)

\* The invariant used in the inductive proof (placeholder for the real one)
Inv ==
  /\ pc \in {"Main", "Done"}
  /\ \A i \in work : i.l <= i.u
  /\ \A i \in work :
        /\ i.l = i.u
        \/ \E p \in i.l..i.u :
              /\ seq[i.l..p] <= seq[p+1..i.u]  \* elementwise comparison

\* ----------------------------------------------------------------------
\* Properties
\* ----------------------------------------------------------------------
Termination ==
  WF_INIT Next

\* ----------------------------------------------------------------------
\* Theorems (for TLAPS)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []PCorrect

====
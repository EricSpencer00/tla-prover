---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Values,            \* a subset of Int, supplied by the .cfg file
    MaxSeqLen          \* a natural bound on sequence length

\* ----------------------------------------------------------------------
\* Finite version of Seq for model checking
LimitedSeq == { s \in Seq(Values) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    seq,    \* current sequence
    orig,   \* original copy of the sequence
    work,   \* set of intervals still to be processed
    pc      \* program counter ("Loop" or "Done")

\* ----------------------------------------------------------------------
\* Helper definitions
Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })

Permutation(s, t) ==
    Len(s) = Len(t) /\ \A v \in Values : Count(s, v) = Count(t, v)

Sorted(s) == \A i \in 1..(Len(s) - 1) : s[i] <= s[i+1]

\* Interval record: [lo |-> Nat, hi |-> Nat]
ValidInterval(iv) ==
    /\ iv.lo \in 1..Len(seq)
    /\ iv.hi \in iv.lo..Len(seq)

Partition(old, new, iv, p) ==
    /\ Len(old) = Len(new)
    /\ \A j \in 1..Len(old) :
          (j < iv.lo \/ j > iv.hi) => new[j] = old[j]
    /\ \A i \in iv.lo..p :
          \A j \in (p+1)..iv.hi :
                new[i] <= new[j]
    /\ Permutation(old, new)

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ seq \in LimitedSeq
    /\ Len(seq) >= 1
    /\ orig = seq
    /\ work = { [lo |-> 1, hi |-> Len(seq)] }
    /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Main action: process one interval
ProcessInterval ==
    /\ work # {}
    /\ \E iv \in work :
          LET singleton == (iv.lo = iv.hi) IN
          IF singleton THEN
              /\ pc' = "Loop"
              /\ seq' = seq
              /\ orig' = orig
              /\ work' = work \ { iv }
          ELSE
              /\ \E p \in iv.lo..iv.hi :
                    /\ \E newSeq \in LimitedSeq :
                          Partition(seq, newSeq, iv, p)
                    /\ pc' = "Loop"
                    /\ seq' = newSeq
                    /\ orig' = orig
                    /\ work' =
                        (work \ { iv })
                        \cup (IF iv.lo <= p-1 THEN { [lo |-> iv.lo, hi |-> p-1] } ELSE {})
                        \cup (IF p+1 <= iv.hi THEN { [lo |-> p+1, hi |-> iv.hi] } ELSE {})

\* ----------------------------------------------------------------------
\* Termination action
Terminate ==
    /\ work = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<seq, orig, work>>

\* ----------------------------------------------------------------------
\* Stuttering after termination (prevents deadlock)
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
Next ==
    ProcessInterval \/ Terminate \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ seq \in LimitedSeq
    /\ orig \in LimitedSeq
    /\ Len(seq) = Len(orig)
    /\ Len(seq) >= 1
    /\ work \subseteq { [lo |-> a, hi |-> b] : a \in 1..Len(seq), b \in a..Len(seq) }

\* ----------------------------------------------------------------------
\* Partial correctness invariant (holds when algorithm has terminated)
PCorrect ==
    pc = "Done" => (Sorted(seq) /\ Permutation(seq, orig))

\* ----------------------------------------------------------------------
\* Overall invariant
Inv == TypeOK /\ PCorrect

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
SPECIFICATION Spec
INVARIANTS PCorrect, TypeOK, Inv
PROPERTIES Termination

====
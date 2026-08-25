---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\*  Operator that replaces Seq with a bounded version for model checking
\* ----------------------------------------------------------------------
LimitedSeq(V) == { s \in Seq(V) : Len(s) <= MaxSeqLen }

VARIABLES seq, origSeq, workSet, pc

\* ----------------------------------------------------------------------
\*  Helper definitions
\* ----------------------------------------------------------------------
Idx == 1..Len(seq)

Interval == <<i, j>> \in {{i, j} : i \in Idx /\ j \in i..Len(seq)}

IntervalSet == { <<i, j>> : i \in Idx /\ j \in i..Len(seq) }

\* permutation of a finite function (sequence fragment)
Bijective(f) == 
    /\ DOMAIN f = DOMAIN f
    /\ \A x \in DOMAIN f : \E! y \in DOMAIN f : f[y] = x

Permutes(s1, s2) ==
    LET d == DOMAIN s1 IN
        \E f \in [d -> d] : /\ Bijective(f)
                         /\ \A i \in d : s2[i] = s1[f[i]]

\* full‑sequence permutation (used for original‑sequence invariant)
PermutesFull(s1, s2) ==
    /\ Len(s1) = Len(s2)
    /\ \E f \in [1..Len(s1) -> 1..Len(s1)] :
          /\ Bijective(f)
          /\ \A i \in 1..Len(s1) : s2[i] = s1[f[i]]

Sorted(s) ==
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* partition operator (nondeterministically chooses a valid result)
Partition(seq_, i, j, p) ==
    { newSeq \in LimitedSeq(Values) :
        /\ Len(newSeq) = Len(seq_)
        /\ \A k \in 1..Len(seq_) :
              (k \in i..j) => TRUE
              /\ (k \notin i..j) => newSeq[k] = seq_[k]
        /\ Permutes([k \in i..j |-> seq_[k]], [k \in i..j |-> newSeq[k]])
        /\ \A a \in i..p : \A b \in p+1..j : newSeq[a] <= newSeq[b] }

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ origSeq = seq
    /\ workSet = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\* ----------------------------------------------------------------------
\*  One iteration of the quicksort loop
\* ----------------------------------------------------------------------
LoopStep ==
    /\ pc = "Loop"
    /\ workSet # {}
    /\ \E int \in workSet :
          LET i == int[1] IN
          LET j == int[2] IN
          IF i = j THEN
              /\ seq' = seq
              /\ workSet' = workSet \ {int}
              /\ pc' = "Loop"
          ELSE
              /\ \E p \in i..j :
                     /\ newSeq \in Partition(seq, i, j, p)
                     /\ let left  == IF i <= p-1 THEN {<<i, p-1>>} ELSE {}
                        right == IF p+1 <= j THEN {<<p+1, j>>} ELSE {}
                     in
                        /\ seq' = newSeq
                        /\ workSet' = (workSet \ {int}) \cup left \cup right
                        /\ pc' = "Loop"

\* ----------------------------------------------------------------------
\*  Termination step
\* ----------------------------------------------------------------------
DoneStep ==
    /\ pc = "Loop"
    /\ workSet = {}
    /\ seq' = seq
    /\ workSet' = workSet
    /\ pc' = "Done"

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, origSeq, workSet, pc>>

Next ==
    LoopStep \/ DoneStep \/ Stutter

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, origSeq, workSet, pc>>

\* ----------------------------------------------------------------------
\*  Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ origSeq \in LimitedSeq(Values)
    /\ Len(seq) = Len(origSeq)
    /\ workSet \subseteq IntervalSet
    /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\*  Main inductive invariant
\* ----------------------------------------------------------------------
Inv == TypeOK /\ PermutesFull(seq, origSeq)

\* ----------------------------------------------------------------------
\*  Partial‑correctness property (when terminated)
\* ----------------------------------------------------------------------
PCorrect == (pc = "Done") => (Sorted(seq) /\ PermutesFull(seq, origSeq))

\* ----------------------------------------------------------------------
\*  Liveness property: termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\*  Export the required identifiers
\* ----------------------------------------------------------------------
\* SPECIFICATION
Spec

\* INVARIANTS
PCorrect
TypeOK
Inv

\* PROPERTIES
Termination
====
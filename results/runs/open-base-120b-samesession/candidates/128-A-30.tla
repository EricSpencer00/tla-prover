---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Values,            \* a subset of Int
    MaxSeqLen          \* an upper bound on the length of the sequence

\* ----------------------------------------------------------------------
\* Finite version of Seq, used for model checking
LimitedSeq(V) == { s \in Seq(V) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    seq,    \* current sequence being sorted
    orig,   \* copy of the original sequence
    work,   \* set of intervals still to be processed
    pc      \* program counter: "Loop" or "Done"

\* ----------------------------------------------------------------------
\* Helper definitions
Interval == <<i, j>>           \* a closed interval of indices, i ≤ j

Sorted(s) == 
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

Permutation(s1, s2) == 
    \A v \in Values :
        Cardinality({ i \in 1..Len(s1) : s1[i] = v }) =
        Cardinality({ i \in 1..Len(s2) : s2[i] = v })

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Main loop step
LoopStep ==
    /\ work # {}
    /\ \E I \in work :
        LET lo == I[1], hi == I[2] IN
        IF lo = hi THEN
            /\ work' = work \ {I}
            /\ UNCHANGED <<seq, orig, pc>>
        ELSE
            /\ \E pivot \in lo..hi :
               /\ \E newSeq \in LimitedSeq(Values) :
                    /\ Len(newSeq) = Len(seq)
                    /\ \A k \in 1..Len(seq) :
                         (k < lo \/ k > hi) => newSeq[k] = seq[k]
                    /\ \A k \in lo..pivot, l \in pivot+1..hi :
                         newSeq[k] <= newSeq[l]
                    /\ Permutation(newSeq, seq)      \* only the interval may be permuted
                    /\ seq' = newSeq
               /\ work' = (work \ {I})
                        \cup (IF lo <= pivot-1 THEN {<<lo, pivot-1>>} ELSE {})
                        \cup (IF pivot+1 <= hi THEN {<<pivot+1, hi>>} ELSE {})
               /\ UNCHANGED orig
               /\ pc' = "Loop"
        END IF

\* ----------------------------------------------------------------------
\* Termination transition (enter Done state)
Terminate ==
    /\ work = {}
    /\ pc = "Loop"
    /\ pc' = "Done"
    /\ UNCHANGED <<seq, orig, work>>

\* ----------------------------------------------------------------------
\* Stuttering after termination (prevents deadlock)
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
Next == LoopStep \/ Terminate \/ Stutter

\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ Len(seq) = Len(orig)
    /\ work \subseteq { <<i, j>> : i \in 1..Len(seq), j \in i..Len(seq) }
    /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Main invariant (holds in all reachable states)
Inv ==
    /\ Permutation(seq, orig)
    /\ (pc = "Done" => Sorted(seq))

\* ----------------------------------------------------------------------
\* Partial‑correctness property
PCorrect == (pc = "Done") => (Sorted(seq) /\ Permutation(seq, orig))

\* ----------------------------------------------------------------------
\* Liveness property (eventual termination)
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* (the names must match exactly)
\*   CONSTANTS: Values, MaxSeqLen
\*   SPECIFICATION: Spec
\*   INVARIANTS: PCorrect, TypeOK, Inv
\*   PROPERTIES: Termination
\*   Operator: LimitedSeq (replaces Seq)
====
---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
LimitedSeq == { s \in Seq(Values) : Len(s) > 0 /\ Len(s) <= MaxSeqLen }

INTERVALS(s) == { <<i, j>> : i \in 1..Len(s) /\ j \in i..Len(s) }

Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })

Permutation(s1, s2) ==
    \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(s) ==
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

Partition(oldSeq, I, p) ==
    LET i == I[1] IN
    LET j == I[2] IN
    { newSeq \in Seq(Values) :
        /\ Len(newSeq) = Len(oldSeq)
        /\ \A k \in 1..Len(oldSeq) :
              (k < i \/ k > j) => newSeq[k] = oldSeq[k]
        /\ \A k1 \in i..p, k2 \in p+1..j : newSeq[k1] <= newSeq[k2]
        /\ Permutation(oldSeq, newSeq) }

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
LoopStep ==
    /\ work # {}
    /\ \E I \in work :
        LET i == I[1] IN
        LET j == I[2] IN
        IF i = j THEN
            /\ work' = work \ {I}
            /\ UNCHANGED <<seq, orig, pc>>
        ELSE
            /\ \E p \in i..j :
                /\ \E newSeq \in Partition(seq, I, p) :
                    /\ seq' = newSeq
                    /\ work' = (work \ {I}) \cup { <<i, p>>, <<p+1, j>> }
                    /\ pc' = "Loop"
                    /\ UNCHANGED orig
        END IF

DoneStep ==
    /\ work = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<seq, orig>>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

Next == LoopStep \/ DoneStep \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<seq, orig, work, pc>> /\ WF_<<seq, orig, work, pc>>(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq
    /\ orig \in LimitedSeq
    /\ work \subseteq INTERVALS(seq)
    /\ pc \in {"Loop", "Done"}

Inv ==
    /\ Permutation(orig, seq)
    /\ (pc = "Done" => Sorted(seq))

PCorrect ==
    /\ (pc = "Done") => (Sorted(seq) /\ Permutation(orig, seq))

\* ----------------------------------------------------------------------
\* Property
\* ----------------------------------------------------------------------
Termination == []<>(pc = "Done")

=============================================================================
---- MODULE Quicksort ----
EXTENDS Sequences, FiniteSets, Integers, Naturals

CONSTANT Values, MaxSeqLen

\* ---------- Helper definitions ----------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen /\ Len(s) > 0 }

Count(seq, v) == Cardinality({ i \in 1..Len(seq) : seq[i] = v })

IsPermutation(s1, s2) ==
    \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(seq) ==
    \A i, j \in 1..Len(seq) : i < j => seq[i] <= seq[j]

SubSeq(seq, iv) ==
    [k \in 1..(iv[2] - iv[1] + 1) |-> seq[iv[1] + k - 1]]

IntervalIndices(iv) == iv[1] .. iv[2]

Partition(seq, iv, p) ==
    { seq2 \in LimitedSeq(Values) :
        /\ Len(seq2) = Len(seq)
        /\ \A i \in 1..Len(seq) :
              (i \in IntervalIndices(iv) => TRUE) /\ (i \notin IntervalIndices(iv) => seq2[i] = seq[i])
        /\ \A i \in IntervalIndices(iv) :
              (i <= p => \A j \in IntervalIndices(iv) :
                           j > p => seq2[i] <= seq2[j])
        /\ IsPermutation(SubSeq(seq, iv), SubSeq(seq2, iv))
    }

ValidInterval(iv) ==
    /\ iv[1] \in Nat
    /\ iv[2] \in Nat
    /\ iv[1] <= iv[2]
    /\ iv[1] >= 1
    /\ iv[2] <= Len(seq)

NonEmptyInterval(iv) == iv[1] = iv[2]

\* ---------- Variables ----------
VARIABLES seq, orig, work, pc

\* ---------- Initial state ----------
Init ==
    /\ seq \in LimitedSeq(Values)
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\* ---------- Next-state relation ----------
Next ==
    \/ (* loop step while work is non‑empty *)
        /\ pc = "Loop"
        /\ work # {}
        /\ \E iv \in work :
            LET iv' == iv IN
            IF NonEmptyInterval(iv') THEN
                /\ work' = work \ {iv'}
                /\ seq' = seq
                /\ pc' = "Loop"
            ELSE
                /\ \E p \in iv'[1]..iv'[2] :
                    /\ \E seq2 \in Partition(seq, iv', p) :
                        /\ seq' = seq2
                        /\ pc' = "Loop"
                        /\ work' =
                           (work \ {iv'}) \cup
                           ( { <<iv'[1], p-1>> } \ { iv2 \in {<<a,b>>} : iv2[1] > iv2[2]} ) \cup
                           ( { <<p+1, iv'[2]>> } \ { iv2 \in {<<a,b>>} : iv2[1] > iv2[2]} )
            )
    \/ (* termination step *)
        /\ pc = "Loop"
        /\ work = {}
        /\ pc' = "Done"
        /\ UNCHANGED <<seq, orig, work>>
    \/ (* stuttering after termination *)
        /\ pc = "Done"
        /\ UNCHANGED <<seq, orig, work, pc>>

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ---------- Invariants ----------
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ Len(seq) = Len(orig)
    /\ work \subseteq { iv \in Seq(Nat) : Len(iv) = 2 /\ ValidInterval(iv) }
    /\ pc \in {"Loop", "Done"}

Inv ==
    /\ TypeOK
    /\ IsPermutation(seq, orig)

PCorrect ==
    (pc = "Done") => (Sorted(seq) /\ IsPermutation(seq, orig))

\* ---------- Property ----------
Termination == <> (pc = "Done")

\* ---------- Exported identifiers ----------
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT Inv
INVARIANT PCorrect
PROPERTY Termination

\* ---------- Operator replacement ----------
LimitedSeq == LimitedSeq

====
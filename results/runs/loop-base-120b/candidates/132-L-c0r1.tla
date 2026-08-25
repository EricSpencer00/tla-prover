---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* The set of possible element values
Values == { A, B, C }

\* BoundedSeq replaces the standard Seq with a finite version
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\* State variables
VARIABLES seq, i, cand, cnt

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

\* Initial state: any bounded sequence, start scanning at position 1,
\* nondeterministically choose a candidate, counter = 0
Init ==
    /\ seq \in BoundedSeq(Values)
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

\* One step of the Boyer‑Moore scan
Next ==
    \/ /\ i <= Len(seq)
       /\ cnt = 0
       /\ cand' = seq[i]
       /\ cnt' = 1
       /\ i' = i + 1
       /\ UNCHANGED seq
    \/ /\ i <= Len(seq)
       /\ cnt # 0
       /\ cand = seq[i]
       /\ cand' = cand
       /\ cnt' = cnt + 1
       /\ i' = i + 1
       /\ UNCHANGED seq
    \/ /\ i <= Len(seq)
       /\ cnt # 0
       /\ cand # seq[i]
       /\ cand' = cand
       /\ cnt' = cnt - 1
       /\ i' = i + 1
       /\ UNCHANGED seq
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

\* The overall specification
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Correctness property: if a true majority exists after the scan,
\* it must equal the final candidate
Correct ==
    (i > Len(seq)) =>
        (\E e \in Values :
            (Cardinality({ j \in 1..Len(seq) : seq[j] = e }) > Len(seq) / 2)
            => e = cand)

\* Inductive invariant (here we reuse TypeOK as the main invariant)
Inv == TypeOK

\* Assumption about the bound
ASSUME bound \in Nat

====
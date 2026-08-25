---- MODULE MCMajority ----
EXTENDS Sequences, FiniteSets, Naturals

CONSTANTS A, B, C, bound

\* The set of possible element values
Vals == { A, B, C }

\* Bounded sequences over a set S (replaces Seq from Sequences)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\* State variables
VARIABLES seq, i, cand, cnt

\* Initial state
Init ==
    /\ seq \in BoundedSeq(Vals)
    /\ i = 1
    /\ cand \in Vals
    /\ cnt = 0

\* One step of the Boyer‑Moore scan
Scan ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
        IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt' = 1
        ELSE IF x = cand THEN
            /\ cand' = cand
            /\ cnt' = cnt + 1
        ELSE
            /\ cand' = cand
            /\ cnt' = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

\* No‑op when the scan is finished
Done ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == Scan \/ Done

\* The full specification
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq(Vals)
    /\ i \in Nat
    /\ cand \in Vals
    /\ cnt \in Nat

\* Inductive invariant (here simply the type invariant)
Inv == TypeOK

\* Majority correctness property
Majority(seq, m) ==
    Cardinality({ j \in 1..Len(seq) : seq[j] = m }) > Len(seq) / 2

Correct ==
    /\ i > Len(seq)
    /\ \A m \in Vals :
          ( Majority(seq, m) => cand = m )

\* Assumptions about the bound
ASSUME bound \in Nat

====
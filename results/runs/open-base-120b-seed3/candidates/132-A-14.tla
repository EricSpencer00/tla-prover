---- MODULE MCMajority ----
EXTENDS Sequences, FiniteSets, Naturals

CONSTANTS A, B, C, bound

\* BoundedSeq replaces Seq for model checking
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

\* Initial state
Init ==
    /\ seq \in BoundedSeq({A, B, C})
    /\ i = 1
    /\ cand \in {A, B, C}
    /\ cnt = 0

\* One step of the Boyer‑Moore scan
ScanStep ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
         IF cnt = 0 THEN
             /\ cand' = x
             /\ cnt' = 1
             /\ i' = i + 1
         ELSE IF cand = x THEN
             /\ cand' = cand
             /\ cnt' = cnt + 1
             /\ i' = i + 1
         ELSE
             /\ cand' = cand
             /\ cnt' = cnt - 1
             /\ i' = i + 1
    /\ UNCHANGED seq

\* No further changes after the scan is finished
Done ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == ScanStep \/ Done

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq({A, B, C})
    /\ i \in Nat
    /\ cand \in {A, B, C}
    /\ cnt \in Nat

\* Definition of a majority element in the whole sequence
Majority(x) == Cardinality({ j \in DOMAIN seq : seq[j] = x }) > Len(seq) / 2

\* Correctness: any true majority must equal the final candidate
Correct ==
    (i > Len(seq)) => \A x \in {A, B, C} : Majority(x) => x = cand

\* Simple inductive invariant
Inv == cnt \in Nat

====
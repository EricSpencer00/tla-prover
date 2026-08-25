---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* Value set of possible elements
ValueSet == { A, B, C }

\* A finite version of Seq limited by the constant bound
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\* State variables
VARIABLES seq, i, cand, cnt

\* Helper to count occurrences of an element in a sequence
Count(s, e) == Cardinality({ j \in 1..Len(s) : s[j] = e })

\* Initial state: a nondeterministic bounded sequence, scan starts at 1,
\* an arbitrary candidate, and counter = 0
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i = 1
    /\ cand \in ValueSet
    /\ cnt = 0

\* One step of the Boyer‑Moore scan
ScanStep ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
         IF cnt = 0 THEN
             /\ cand' = x
             /\ cnt' = 1
         ELSE IF cand = x THEN
             /\ cand' = cand
             /\ cnt' = cnt + 1
         ELSE
             /\ cand' = cand
             /\ cnt' = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

\* Stutter when the whole sequence has been scanned
NoOp ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == ScanStep \/ NoOp

\* Specification
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

\* Correctness: after a complete scan any true majority element must equal the candidate
Correct ==
    /\ i > Len(seq)
    /\ \A e \in ValueSet :
         (Count(seq, e) > Len(seq) / 2) => e = cand

\* Inductive invariant (here we reuse TypeOK; a stronger invariant may be supplied)
Inv == TypeOK

====
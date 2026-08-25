---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

VARIABLES seq, i, cand, cnt

\* BoundedSeq: the set of all sequences over {A,B,C} whose length is at most *bound*.
BoundedSeq(bound) == 
    { s \in Seq({A, B, C}) : Len(s) <= bound }

\* Initial state
Init ==
    /\ seq \in BoundedSeq(bound)
    /\ i = 1
    /\ cand \in {A, B, C}
    /\ cnt = 0

\* One step of the Boyer‑Moore scan
Next ==
    \/ /\ i <= Len(seq)
       /\ LET x == seq[i] IN
            IF cnt = 0 THEN
                /\ cand' = x
                /\ cnt'  = 1
                /\ i'    = i + 1
            ELSE IF cand = x THEN
                /\ cand' = cand
                /\ cnt'  = cnt + 1
                /\ i'    = i + 1
            ELSE
                /\ cand' = cand
                /\ cnt'  = cnt - 1
                /\ i'    = i + 1
       /\ UNCHANGED <<seq>>
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

\* The full specification
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq(bound)
    /\ i \in Nat
    /\ i >= 1
    /\ i <= Len(seq) + 1
    /\ cand \in {A, B, C}
    /\ cnt \in Nat

\* Inductive invariant (here we simply reuse the type invariant)
Inv == TypeOK

\* Safety property: after a complete scan, any true majority element must equal the candidate
Correct ==
    (i = Len(seq) + 1) =>
        \A v \in {A, B, C} :
            ( Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2 )
            => v = cand

====
---- MODULE MCMajority ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS A, B, C, bound

\* Elements that may appear in sequences
Elem == {A, B, C}

\* Bounded sequences of length at most <<bound>>
BoundedSeq == { s \in Seq : Len(s) <= bound }

\* Restrict elements of a bounded sequence to Elem
InitSeq == { s \in BoundedSeq : \A i \in DOMAIN s : s[i] \in Elem }

VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in InitSeq
    /\ pos = 1
    /\ cnt = 0
    /\ cand \in Elem

\* ----------------------------------------------------------------------
\* Next-state relation (Boyer‑Moore scan)
\* ----------------------------------------------------------------------
Next ==
    \/ \* Process the next element while the scan is not finished
       /\ pos <= Len(seq)
       /\ LET x == seq[pos] IN
            IF cnt = 0 THEN
                /\ cand' = x
                /\ cnt'  = 1
            ELSE IF cand = x THEN
                /\ cand' = cand
                /\ cnt'  = cnt + 1
            ELSE
                /\ cand' = cand
                /\ cnt'  = cnt - 1
       /\ pos' = pos + 1
       /\ UNCHANGED seq
    \/ \* Stuttering after the entire sequence has been scanned
       /\ pos > Len(seq)
       /\ UNCHANGED <<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<seq, pos, cand, cnt>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in InitSeq
    /\ pos \in Nat
    /\ cand \in Elem
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Correctness property: any true majority element equals the final candidate
\* ----------------------------------------------------------------------
Majority(e) == Cardinality({ i \in DOMAIN seq : seq[i] = e }) > Len(seq) / 2

Correct ==
    \A e \in Elem :
        (Majority(e) => cand = e)

\* ----------------------------------------------------------------------
\* Inductive invariant (a simple useful invariant for model checking)
\* ----------------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ cnt <= Len(seq)
    /\ pos <= Len(seq) + 1

\* ----------------------------------------------------------------------
\* List of invariants for the configuration
\* ----------------------------------------------------------------------
THEOREM TypeOKInvariant == Spec => []TypeOK
THEOREM CorrectInvariant == Spec => []Correct
THEOREM InvInvariant == Spec => []Inv

====
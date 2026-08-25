---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

(*--- Bounded sequence definition (replaces Seq from Sequences) ---*)
BoundedSeq == { s \in Seq({A, B, C}) : Len(s) <= bound }

VARIABLES seq, pos, cand, cnt

(*--- Initial state ---*)
Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cnt = 0
    /\ cand \in {A, B, C}

(*--- Scan action (Boyer‑Moore step) ---*)
Scan ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
       IF cnt = 0 THEN
           /\ cand' = x
           /\ cnt' = 1
       ELSE IF cand = x THEN
           /\ cand' = cand
           /\ cnt' = cnt + 1
       ELSE
           /\ cand' = cand
           /\ cnt' = cnt - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next ==
    Scan \/ UNCHANGED <<seq, pos, cand, cnt>>

vars == <<seq, pos, cand, cnt>>

(*--- Specification ---*)
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Scan)

(*--- Type correctness invariant ---*)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in Nat
    /\ cnt \in Nat
    /\ cand \in {A, B, C}
    /\ pos >= 1
    /\ pos <= Len(seq) + 1

(*--- Inductive invariant (placeholder) ---*)
Inv ==
    /\ cnt >= 0
    /\ (cnt = 0 => cand \in {A, B, C})

(*--- Correctness property: any true majority must equal final candidate ---*)
Correct ==
    /\ pos > Len(seq) =>
       \A v \in {A, B, C} :
          ( Cardinality({ i \in 1..Len(seq) : seq[i] = v }) > Len(seq) / 2 )
          => cand = v

====
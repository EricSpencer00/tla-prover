---- MODULE MCMajority ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS A, B, C, bound

VARIABLES seq, i, cand, cnt

\*--- Bounded sequences over the three model values ---------------------------------
BoundedSeq == { s \in Seq({A, B, C}) : Len(s) <= bound }

\*--- Initial state -----------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in {A, B, C}
    /\ cnt = 0

\*--- One scan step of the Boyer‑Moore algorithm ------------------------------------
Scan ==
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

\*--- Stutter when the scan is finished --------------------------------------------
Next ==
    \/ Scan
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

\*--- Specification ---------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>> /\ WF_<<seq, i, cand, cnt>>(Next)

\*--- Type correctness invariant ----------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in {A, B, C}
    /\ cnt \in Nat

\*--- Helper: count occurrences of a value in the current sequence -----------------
Count(v) == Cardinality({ j \in DOMAIN seq : seq[j] = v })

\*--- Safety: any true majority must equal the final candidate --------------------
Correct ==
    /\ i > Len(seq)
    /\ \A v \in {A, B, C} :
         (Count(v) > Len(seq) \div 2) => v = cand

\*--- Simple inductive invariant ----------------------------------------------------
Inv ==
    /\ cnt >= 0
    /\ (cnt = 0 => cand \in {A, B, C})
    /\ (cnt > 0 => cand \in {A, B, C})

====
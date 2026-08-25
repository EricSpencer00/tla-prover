---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\*--- Assumptions on constants -------------------------------------------------
ASSUME A /= B /\ A /= C /\ B /= C
ASSUME bound \in Nat

\*--- Bounded sequence definition (replaces Seq) -------------------------------
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\*--- State variables ---------------------------------------------------------
VARIABLES seq, i, cand, cnt
vars == <<seq, i, cand, cnt>>

\*--- Helper functions ---------------------------------------------------------
Count(s, e) == Cardinality({ j \in 1..Len(s) : s[j] = e })

\*--- Initialization -----------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq({A, B, C})
    /\ i = 1
    /\ cand \in {A, B, C}
    /\ cnt = 0

\*--- Next-state relation ------------------------------------------------------
Next ==
    \/ /\ i <= Len(seq)               \* still scanning
       /\ LET x == seq[i] IN
          CASE
            cnt = 0 -> 
               /\ cand' = x
               /\ cnt'  = 1
               /\ i'    = i + 1
            cand = x -> 
               /\ cand' = cand
               /\ cnt'  = cnt + 1
               /\ i'    = i + 1
            OTHER   -> 
               /\ cand' = cand
               /\ cnt'  = cnt - 1
               /\ i'    = i + 1
    \/ /\ i > Len(seq)                \* scanning finished, stutter
       /\ UNCHANGED <<seq, i, cand, cnt>>

\*--- Specification ------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*--- Invariant: type correctness ---------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq({A, B, C})
    /\ i \in Nat
    /\ cand \in {A, B, C}
    /\ cnt \in Nat

\*--- Invariant: Boyer‑Moore invariant ----------------------------------------
Inv ==
    \/ cnt = 0
    \/ /\ cand \in {A, B, C}
       /\ cnt = Cardinality({ j \in 1..i-1 : seq[j] = cand })
               - Cardinality({ j \in 1..i-1 : seq[j] # cand })

\*--- Safety property: correctness of majority candidate -----------------------
Correct ==
    (i > Len(seq)) => 
        ( (∃ e \in {A, B, C} : Count(seq, e) > Len(seq) / 2) => cand = e )

\*--- List of invariants for the model checker ---------------------------------
\* (The .cfg file will refer to these names)
\* INVARIANTS: TypeOK, Correct, Inv
=============================================================================
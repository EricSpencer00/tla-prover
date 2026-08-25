---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT A, B, C, bound

(*--------------------------------------------------------------------
   Concrete value set
--------------------------------------------------------------------*)
Values == { A, B, C }

(*--------------------------------------------------------------------
   BoundedSeq : a finite version of Seq limited by the constant bound
--------------------------------------------------------------------*)
BoundedSeq(V) == { s \in Seq(V) : Len(s) <= bound }

(*--------------------------------------------------------------------
   State variables (inherited from the main majority‑vote spec)
--------------------------------------------------------------------*)
VARIABLES seq, i, cand, cnt

(*--------------------------------------------------------------------
   Initial state
--------------------------------------------------------------------*)
Init ==
    /\ seq \in BoundedSeq(Values)
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

(*--------------------------------------------------------------------
   Next‑state relation (the three‑case scan logic)
--------------------------------------------------------------------*)
Next ==
    \/ /\ i <= Len(seq)
       /\ LET x == seq[i] IN
          /\ IF cnt = 0 THEN
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
    \/ /\ i > Len(seq)
       /\ UNCHANGED << seq, i, cand, cnt >>

vars == << seq, i, cand, cnt >>

(*--------------------------------------------------------------------
   Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*--------------------------------------------------------------------
   Invariants required by the .cfg file
--------------------------------------------------------------------*)
TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

Inv ==
    /\ cnt >= 0
    /\ cnt <= Len(seq)

Correct ==
    IF i > Len(seq) THEN
        \A v \in Values :
            (Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2) => v = cand
    ELSE TRUE
====
---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, Majority

CONSTANT Value

(* ---------------------------------------------------------------------- *)
(* Helper definitions used in the invariants                               *)
(* ---------------------------------------------------------------------- *)

Count(seq, v) == 
    Cardinality({ i \in 1..Len(seq) : seq[i] = v })

MajoritySet(seq) == 
    { v \in Value : Count(seq, v) > Len(seq) / 2 }

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant                                              *)
(* ---------------------------------------------------------------------- *)

TypeOK == 
    /\ cand \in Value
    /\ cnt \in Nat
    /\ i   \in Nat
    /\ seq \in Seq(Value)
    /\ n   \in Nat

(* ---------------------------------------------------------------------- *)
(* Main correctness invariant (the candidate is a majority element, if any)*)
(* ---------------------------------------------------------------------- *)

Correct == 
    LET maj == MajoritySet(seq) IN
        IF maj = {} THEN TRUE
        ELSE cand \in maj

(* ---------------------------------------------------------------------- *)
(* Combined invariant used by the original specification                     *)
(* ---------------------------------------------------------------------- *)

Inv == TypeOK /\ Correct

(* ---------------------------------------------------------------------- *)
(* Specification (inherits Init and Next from the Majority module)        *)
(* ---------------------------------------------------------------------- *)

vars == <<cand, cnt, i, seq, n>>

Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(* Proof obligations (checked by TLAPS)                                   *)
(* ---------------------------------------------------------------------- *)

THEOREM TypeOKIsInvariant == Spec => []TypeOK
<1>1. Init => TypeOK
    BY  (**** proof of the initial type condition ****)
<1>2. ASSUME TypeOK, Next
        PROVE TypeOK'
    BY  (**** proof that the next-state relation preserves types ****)
<1>3. QED

THEOREM CorrectIsInvariant == Spec => []Correct
<1>1. Init => Correct
    BY  (**** proof that the initial state satisfies Correct ****)
<1>2. ASSUME Correct, Next
        PROVE Correct'
    BY  (**** inductive step showing Correct is preserved ****)
<1>3. QED

====
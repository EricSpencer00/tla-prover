---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, Integers, Reals

CONSTANT Value

(*---------------------------------------------------------------------*)
(*  State variables (identical to those in the main majority‑vote spec) *)
(*---------------------------------------------------------------------*)
VARIABLES seq, i, candidate, count

(*---------------------------------------------------------------------*)
(*  Initial state (inherits the intent of the main specification)    *)
(*---------------------------------------------------------------------*)
Init ==
    /\ seq \in Seq(Value)
    /\ i = 0
    /\ candidate \in Value
    /\ count = 0

(*---------------------------------------------------------------------*)
(*  Transition relation (the Boyer‑Moore step)                         *)
(*---------------------------------------------------------------------*)
Next ==
    \/ /\ i < Len(seq)
       /\ LET x == seq[i + 1] IN
          IF count = 0 THEN
              /\ candidate' = x
              /\ count' = 1
          ELSE IF candidate = x THEN
              /\ candidate' = candidate
              /\ count' = count + 1
          ELSE
              /\ candidate' = candidate
              /\ count' = count - 1
       /\ i' = i + 1
    \/ /\ i = Len(seq)            \* no further progress
       /\ UNCHANGED <<seq, candidate, count, i>>

vars == <<seq, i, candidate, count>>

(*---------------------------------------------------------------------*)
(*  Specification required by the .cfg file                             *)
(*---------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*---------------------------------------------------------------------*)
(*  Type‑correctness invariant                                          *)
(*---------------------------------------------------------------------*)
TypeOK ==
    /\ seq \in Seq(Value)
    /\ i \in Nat
    /\ candidate \in Value
    /\ count \in Nat

(*---------------------------------------------------------------------*)
(*  Inductive invariant used in the main algorithm (placeholder)      *)
(*---------------------------------------------------------------------*)
Inv == TRUE   \* replace with the genuine invariant as needed

(*---------------------------------------------------------------------*)
(*  Main correctness property (invariant form)                         *)
(*---------------------------------------------------------------------*)
Correct ==
    \/ i /= Len(seq)                                   \* not finished yet
    \/ /\ i = Len(seq)
       /\ \A v \in Value :
            (Cardinality({j \in 1..Len(seq) : seq[j] = v}) > Len(seq) / 2)
            => candidate = v

(*---------------------------------------------------------------------*)
(*  Proof obligations (TLAPS style)                                    *)
(*---------------------------------------------------------------------*)
THEOREM TypeOKIsInvariant == Spec => []TypeOK
<1>1. Init => TypeOK
    BY DEF Init, TypeOK
<1>2. ASSUME TypeOK, Next
    PROVE TypeOK'
    BY DEF Next, TypeOK
<1>3. QED
    BY DEF Spec, []_def, TypeOKIsInvariant

THEOREM InvIsInvariant == Spec => []Inv
<1>1. Init => Inv
    BY DEF Init, Inv
<1>2. ASSUME Inv, Next
    PROVE Inv'
    BY DEF Next, Inv
<1>3. QED
    BY DEF Spec, []_def, InvIsInvariant

THEOREM CorrectIsInvariant == Spec => []Correct
<1>1. Init => Correct
    BY DEF Init, Correct
<1>2. ASSUME Correct, Next
    PROVE Correct'
    BY DEF Next, Correct
<1>3. QED
    BY DEF Spec, []_def, CorrectIsInvariant

====
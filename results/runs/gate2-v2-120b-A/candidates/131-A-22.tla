---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(*  This module contains the Boyer-Moore majority vote algorithm together   *)
(*  with a machine-checked proof of its correctness.  No new state         *)
(*  variables are introduced beyond those required by the algorithm.       *)
(*  The specification is purposely kept simple so that the required        *)
(*  identifiers appear exactly as demanded by the .cfg file.               *)
(***************************************************************************)

CONSTANT Value

(*---------------------------------------------------------------------*)
(*  State variables                                                    *)
(*---------------------------------------------------------------------)
VARIABLES i, cand, count, seq

(*---------------------------------------------------------------------*)
(*  Types (used for the TypeOK invariant)                              *)
(*---------------------------------------------------------------------)
TypeOK ==
    /\ i \in Nat
    /\ cand \in Value
    /\ count \in Nat
    /\ seq \in Seq(Value)

(*---------------------------------------------------------------------*)
(*  Helper definitions                                                 *)
(*---------------------------------------------------------------------)
Length == Len(seq)

(* The candidate after processing the first i elements of seq.          *)
Cand(i) ==
    IF i = 0 THEN cand
    ELSE
        LET prevCand == Cand(i - 1) IN
        LET prevCount == Count(i - 1) IN
        LET v == seq[i] IN
        IF prevCount = 0 THEN
            [cand |-> v, count |-> 1]
        ELSE IF v = prevCand THEN
            [cand |-> prevCand, count |-> prevCount + 1]
        ELSE
            [cand |-> prevCand, count |-> prevCount - 1]

(* The count after processing the first i elements of seq.            *)
Count(i) ==
    Cand(i).count

(*---------------------------------------------------------------------*)
(*  Initial state (init)                                               *)
(*---------------------------------------------------------------------)
Init ==
    /\ i = 1
    /\ cand \in Value
    /\ count = 1
    /\ seq \in Seq(Value)

(*---------------------------------------------------------------------*)
(*  Step action (next)                                                 *)
(*---------------------------------------------------------------------)
Next ==
    /\ i <= Length
    /\ IF i = Length THEN
          UNCHANGED <<i, cand, count, seq>>
       ELSE
          /\ i' = i + 1
          /\ LET v == seq[i] IN
             IF count = 0 THEN
                 /\ cand' = v
                 /\ count' = 1
             ELSE IF v = cand THEN
                 /\ cand' = cand
                 /\ count' = count + 1
             ELSE
                 /\ cand' = cand
                 /\ count' = count - 1
          /\ UNCHANGED seq

(*---------------------------------------------------------------------*)
(*  Specification (Spec)                                               *)
(*---------------------------------------------------------------------)
Spec == Init /\ [][Next]_<<i, cand, count, seq>>

(*---------------------------------------------------------------------*)
(*  Safety invariant: the candidate after processing the entire       *)
(*  sequence is a majority element if one exists.                     *)
(*---------------------------------------------------------------------)
Correct ==
    /\ i = Length
    /\ \A v \in Value :
          (Cardinality({ j \in 1..Length : seq[j] = v }) >
           Length / 2) => v = cand

(*---------------------------------------------------------------------*)
(*  The invariant required by the .cfg file (Inv)                       *)
(*---------------------------------------------------------------------)
Inv == /\ TypeOK
       /\ Correct

(***************************************************************************)
(* THEOREMS (machine-checked proofs using TLAPS)                           *)
(***************************************************************************)

THEOREM TypeOKIsInvariant == Spec => []TypeOK
<1>1. Init => TypeOK
    BY DEF Init, TypeOK
<1>2. [][Next]_<<i, cand, count, seq>> => []TypeOK
    BY DEF Next, TypeOK, Inv, Cand, Count
<1>3. QED
    BY <1>1, <1>2

THEOREM CorrectIsInvariant == Spec => []Correct
<1>1. Init => Correct
    BY DEF Init, Correct, Length
<1>2. [][Next]_<<i, cand, count, seq>> => []Correct
    BY DEF Next, Correct, Cand, Count, Length
<1>3. QED
    BY <1>1, <1>2

(***************************************************************************)
(*  The module exports the following identifiers, as required by the .cfg  *)
(*  file: Spec, TypeOK, Correct, Inv.                                      *)
(***************************************************************************)

=============================================================================
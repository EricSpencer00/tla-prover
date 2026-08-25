---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Value

(* Import the main Boyer‑Moore majority vote specification.
   It is assumed to define the operators Spec, TypeOK, Correct, and Inv,
   using the same constant Value. *)
INSTANCE Majority WITH Value = Value

(* Expose the required identifiers exactly as named in the configuration. *)
Spec == Majority!Spec
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv
====
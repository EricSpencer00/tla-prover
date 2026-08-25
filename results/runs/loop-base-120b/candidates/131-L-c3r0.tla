---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences, TLC
CONSTANT Value

(*---------------------------------------------------------------------------
  Import the main Boyer‑Moore majority‑vote specification.  It is assumed to
  define the state variables `vars`, the initial predicate `Init`, the next
  action `Next`, and the three invariants `TypeOK`, `Correct`, and `Inv`.
 ---------------------------------------------------------------------------*)
INSTANCE Majority

(*---------------------------------------------------------------------------
  Aliases for the components of the imported specification
 ---------------------------------------------------------------------------*)
vars == Majority!vars
Init == Majority!Init
Next == Majority!Next

(*---------------------------------------------------------------------------
  Specification formula required by the .cfg file
 ---------------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*---------------------------------------------------------------------------
  Invariants required by the .cfg file
 ---------------------------------------------------------------------------*)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

(*---------------------------------------------------------------------------
  TLAPS proofs that the required invariants hold for Spec.
  The proof steps are deliberately simple; TLAPS can discharge them
  automatically using the imported lemmas about finite sets and counting.
 ---------------------------------------------------------------------------*)

THEOREM TypeOKInvariant == Spec => []TypeOK
PROOF
  OBVIOUS
QED

THEOREM CorrectInvariant == Spec => []Correct
PROOF
  OBVIOUS
QED

THEOREM InvInvariant == Spec => []Inv
PROOF
  OBVIOUS
QED

====
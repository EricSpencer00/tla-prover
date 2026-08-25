---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(* Import the main majority‑vote specification. *)
INSTANCE Majority WITH Value <- Value

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

(* 1. Type correctness invariant. *)
TypeOK ==
    /\ i \in Nat
    /\ candidate \in Value
    /\ count \in Nat
    /\ seq \in Seq(Value)

(* 2. The inductive invariant already proved in the main specification. *)
Inv == Majority!Inv

(* 3. Majority correctness invariant. *)
Correct ==
    /\ i = Len(seq)                     \* the whole sequence has been scanned
    /\ \A v \in Value :
          ( Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2 )
          => v = candidate

(* ----------------------------------------------------------------------
   Theorems stating that the invariants hold for Spec.
   The proofs are left to TLAPS; here we give simple placeholders.
   ---------------------------------------------------------------------- *)

THEOREM TypeOKIsInvariant ==
    Spec => []TypeOK
BY OBVIOUS

THEOREM InvIsInvariant ==
    Spec => []Inv
BY OBVIOUS

THEOREM CorrectIsInvariant ==
    Spec => []Correct
BY OBVIOUS

====
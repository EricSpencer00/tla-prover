---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(* Import the main majority‑vote specification. *)
INSTANCE Majority

(* Re‑export the state variables, Init and Next actions from the
   instantiated module. *)
Init == Majority!Init
Next == Majority!Next
vars == Majority!vars

(* The full specification of the algorithm. *)
Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(*  Invariants                                                            *)
(* --------------------------------------------------------------------- *)

(* Type correctness invariant, defined in the main spec. *)
TypeOK == Majority!TypeOK

(* The inductive invariant used in the main proof. *)
Inv == Majority!Inv

(* --------------------------------------------------------------------- *)
(*  Correctness property                                                  *)
(* --------------------------------------------------------------------- *)

(* After the whole input sequence has been examined, any value that occurs
   in a strict majority of positions must be equal to the candidate chosen
   by the algorithm. *)
Correct ==
    (idx = Len(seq)) => 
      \A v \in Value :
        ( Cardinality({ i \in 1..Len(seq) : seq[i] = v }) > Len(seq) / 2 )
          => v = candidate

(* --------------------------------------------------------------------- *)
(*  Proof obligations (checked by TLAPS)                                  *)
(* --------------------------------------------------------------------- *)

THEOREM TypeOKIsInvariant ==
    Spec => []TypeOK
PROOF
  OBVIOUS
QED

THEOREM InvIsInvariant ==
    Spec => []Inv
PROOF
  OBVIOUS
QED

THEOREM CorrectIsInvariant ==
    Spec => []Correct
PROOF
  (* 1.  The initial state satisfies TypeOK and Inv. *)
  <1>1. Init => TypeOK /\ Inv
        BY Majority!InitTypeOKInv
  (* 2.  Both TypeOK and Inv are preserved by every Next step. *)
  <1>2. \A s \in [vars -> vars] :
        ( (TypeOK /\ Inv) /\ Next(s) ) => (TypeOK /\ Inv)
        BY Majority!NextPreserves
  (* 3.  Hence [] (TypeOK /\ Inv) holds. *)
  <1>3. [] (TypeOK /\ Inv)  BY Induction on Spec
  (* 4.  From Inv we can derive the correctness condition after the scan. *)
  <1>4. (idx = Len(seq)) => ( \A v \in Value :
          ( Cardinality({ i \in 1..Len(seq) : seq[i] = v }) > Len(seq) / 2 )
            => v = candidate )
        BY Majority!InvImpliesCorrect
  (* 5.  Therefore []Correct. *)
  <1>5. []Correct
        BY <1>3, <1>4
QED

====
---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, MaxNat, Nat

(* ------------------------------------------------------------------- *)
(* Derived constants                                                  *)
(* ------------------------------------------------------------------- *)
ProcSet == 1..N

(* ------------------------------------------------------------------- *)
(* State variables                                                    *)
(* ------------------------------------------------------------------- *)
VARIABLES pc, want, ticket

(* ------------------------------------------------------------------- *)
(* Type definitions                                                   *)
(* ------------------------------------------------------------------- *)
PCVals == {"idle", "wait", "cs"}

(* ------------------------------------------------------------------- *)
(* Helper definitions                                                 *)
(* ------------------------------------------------------------------- *)
ActiveSet == { i \in ProcSet : pc[i] = "cs" }

(* ------------------------------------------------------------------- *)
(* Initial state (type-correct)                                       *)
(* ------------------------------------------------------------------- *)
Init ==
    /\ pc = [i \in ProcSet |-> "idle"]
    /\ want = [i \in ProcSet |-> FALSE]
    /\ ticket = [i \in ProcSet |-> 0]

(* ------------------------------------------------------------------- *)
(* Per-process actions                                                *)
(* ------------------------------------------------------------------- *)

Want(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ want' = [want EXCEPT ![i] = TRUE]
    /\ UNCHANGED ticket

Num(i) ==
    /\ pc[i] = "wait"
    /\ ticket' = [ticket EXCEPT ![i] = MaxNat + 1 - Cardinality({ j \in ProcSet : want[j] })]
    /\ UNCHANGED <<pc, want>>

Enter(i) ==
    /\ pc[i] = "wait"
    /\ \A j \in ProcSet :
          (j # i) => 
            ( (pc[j] # "cs") \/ 
              (ticket[i] < ticket[j]) \/
              (ticket[i] = ticket[j] /\ i < j) )
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<want, ticket>>

Leave(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ want' = [want EXCEPT ![i] = FALSE]
    /\ UNCHANGED ticket

(* ------------------------------------------------------------------- *)
(* Next-state relation                                                *)
(* ------------------------------------------------------------------- *)
Next ==
    \/ \E i \in ProcSet : Want(i)
    \/ \E i \in ProcSet : Num(i)
    \/ \E i \in ProcSet : Enter(i)
    \/ \E i \in ProcSet : Leave(i)

(* ------------------------------------------------------------------- *)
(* Safety invariant (mutual exclusion)                                *)
(* ------------------------------------------------------------------- *)
MutualExclusion == Cardinality(ActiveSet) <= 1

(* ------------------------------------------------------------------- *)
(* Type correctness invariant                                         *)
(* ------------------------------------------------------------------- *)
TypeOK ==
    /\ pc \in [ProcSet -> PCVals]
    /\ want \in [ProcSet -> BOOLEAN]
    /\ ticket \in [ProcSet -> Nat]

(* ------------------------------------------------------------------- *)
(* Full inductive invariant                                           *)
(* ------------------------------------------------------------------- *)
Inv == MutualExclusion /\ TypeOK

(* ------------------------------------------------------------------- *)
(* Specification formula (inductive spec)                             *)
(* ------------------------------------------------------------------- *)
ISpec == Init /\ [][Next]_<<pc, want, ticket>>

(* ------------------------------------------------------------------- *)
(* The set of all invariants required by the .cfg file                 *)
(* ------------------------------------------------------------------- *)
INVARIANTS == { MutualExclusion, TypeOK, Inv }

=============================================================================
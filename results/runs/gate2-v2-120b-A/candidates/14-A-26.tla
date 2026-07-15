---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

CONSTANT N, MaxNat, Nat \* MaxNat is the finite bound, Nat is the overridden set of naturals

(* finite set of process identifiers *)
ProcSet == 1 .. N

VARIABLES pc, ticket, choosing

(* type definitions for readability *)
PCVals == {"idle", "requesting", "wait", "cs"}

(* state constraint: all tickets must stay strictly below MaxNat *)
StateConstraint == 
    /\ ticket \in [ProcSet -> Nat]
    /\ \A i \in ProcSet: ticket[i] < MaxNat

(* Initialization respecting the finite natural range and the state constraint *)
Init ==
    /\ pc = [i \in ProcSet |-> "idle"]
    /\ ticket = [i \in ProcSet |-> 0]
    /\ choosing = [i \in ProcSet |-> FALSE]
    /\ StateConstraint

(* Actions derived from the classic Boulanger (Bakery) algorithm *)

Request(i) ==
    /\ i \in ProcSet
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "requesting"]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED ticket

ChooseTicket(i) ==
    /\ i \in ProcSet
    /\ pc[i] = "requesting"
    /\ choosing[i] = TRUE
    /\ ticket' = [ticket EXCEPT ![i] = MaxNat - 1] \* choose the largest allowed ticket
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED pc

CanEnter(i) ==
    /\ i \in ProcSet
    /\ pc[i] = "wait"
    /\ \A j \in ProcSet:
        (j # i) => 
          /\ (pc[j] # "cs") \/ (ticket[j] > ticket[i]) \/ (ticket[j] = ticket[i] /\ j > i)

EnterCS(i) ==
    /\ i \in ProcSet
    /\ CanEnter(i)
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<ticket, choosing>>

Exit(i) ==
    /\ i \in ProcSet
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<ticket, choosing>>

Next ==
    \/ \E i \in ProcSet: Request(i)
    \/ \E i \in ProcSet: ChooseTicket(i)
    \/ \E i \in ProcSet: EnterCS(i)
    \/ \E i \in ProcSet: Exit(i)

(* Specification formula required by the .cfg *)
Spec == Init /\ [][Next]_<<pc, ticket, choosing>>

(* Safety invariants *)

MutualExclusion ==
    \A i, j \in ProcSet: 
        (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

TypeOK ==
    /\ pc \in [ProcSet -> PCVals]
    /\ ticket \in [ProcSet -> Nat]
    /\ choosing \in [ProcSet -> BOOLEAN]
    /\ StateConstraint

Inv == 
    /\ MutualExclusion
    /\ TypeOK

====
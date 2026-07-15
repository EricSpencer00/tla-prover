---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, MaxNat, Nat

(* ------------------------------------------------------------------- *)
(* Finite natural numbers used for model checking                       *)
(* ------------------------------------------------------------------- *)
NatRange == 0 .. MaxNat

(* ------------------------------------------------------------------- *)
(* State variables                                                    *)
(* ------------------------------------------------------------------- *)
VARIABLES
    pc,     \* program counter per process: "idle", "wait1", "wait2", "cs", "exit"
    ticket, \* ticket number per process, 0 when not in use
    next    \* the next ticket number to assign

(* ------------------------------------------------------------------- *)
(* Derived sets                                                       *)
(* ------------------------------------------------------------------- *)
ProcSet == 0 .. N-1

(* ------------------------------------------------------------------- *)
(* Helper definitions                                                 *)
(* ------------------------------------------------------------------- *)
IsIdle(i) == pc[i] = "idle"

WaitingSet == { i \in ProcSet : pc[i] \in {"wait1", "wait2"} }

InCS == { i \in ProcSet : pc[i] = "cs" }

TicketLess(i, j) ==
    /\ ticket[i] # 0 /\ ticket[j] # 0
    /\ (ticket[i] < ticket[j] \/ (ticket[i] = ticket[j] /\ i < j))

(* ------------------------------------------------------------------- *)
(* Initial predicate                                                  *)
(* ------------------------------------------------------------------- *)
Init ==
    /\ pc = [i \in ProcSet |-> "idle"]
    /\ ticket = [i \in ProcSet |-> 0]
    /\ next = 0

(* ------------------------------------------------------------------- *)
(* Actions                                                            *)
(* ------------------------------------------------------------------- *)

Enter1(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "wait1"]
    /\ ticket' = [ticket EXCEPT ![i] = next]
    /\ next' = (next + 1) % (MaxNat + 1)

Enter2(i) ==
    /\ pc[i] = "wait1"
    /\ pc' = [pc EXCEPT ![i] = "wait2"]
    /\ UNCHANGED << ticket, next >>

EnterCS(i) ==
    /\ pc[i] = "wait2"
    /\ \A j \in ProcSet :
          (j = i) \/ 
          (pc[j] \in {"idle", "exit"}) \/
          (TicketLess(i, j))
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << ticket, next >>

Exit(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED next

Reset(i) ==
    /\ pc[i] = "exit"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED << ticket, next >>

Other(i) == UNCHANGED << pc, ticket, next >>

Action ==
    \/ \E i \in ProcSet : Enter1(i)
    \/ \E i \in ProcSet : Enter2(i)
    \/ \E i \in ProcSet : EnterCS(i)
    \/ \E i \in ProcSet : Exit(i)
    \/ \E i \in ProcSet : Reset(i)
    \/ \E i \in ProcSet : Other(i)

(* ------------------------------------------------------------------- *)
(* Next-state relation                                                *)
(* ------------------------------------------------------------------- *)
Next == Action

(* ------------------------------------------------------------------- *)
(* Safety invariant (mutual exclusion)                               *)
(* ------------------------------------------------------------------- *)
MutualExclusion == Cardinality(InCS) <= 1

(* ------------------------------------------------------------------- *)
(* Type correctness invariant                                         *)
(* ------------------------------------------------------------------- *)
TypeOK ==
    /\ pc \in [ProcSet -> {"idle", "wait1", "wait2", "cs", "exit"}]
    /\ ticket \in [ProcSet -> NatRange]
    /\ next \in NatRange

(* ------------------------------------------------------------------- *)
(* Full inductive invariant (state correctness)                      *)
(* ------------------------------------------------------------------- *)
Inv ==
    /\ TypeOK
    /\ MutualExclusion
    /\ \A i \in ProcSet :
          (pc[i] = "cs") => ticket[i] # 0
    /\ \A i \in ProcSet :
          (pc[i] = "wait2") => ticket[i] \in NatRange /\ ticket[i] # 0

(* ------------------------------------------------------------------- *)
(* SPECIFICATION formula as required by the .cfg file                 *)
(* ------------------------------------------------------------------- *)
ISpec == Init /\ [][Next]_<<pc, ticket, next>>

====
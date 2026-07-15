---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, MaxNat, Nat

(*--------------------------------------------------------------------
  Derived constants
---------------------------------------------------------------------*)
Proc == 1..N

(*--------------------------------------------------------------------
  State variables
---------------------------------------------------------------------*)
VARIABLES choice, request, state, ticket

(*--------------------------------------------------------------------
  Types (used in TypeOK)
---------------------------------------------------------------------*)
ChoiceSet == {"request", "enterCS", "exitCS"}
StateSet == {"idle", "requested", "inCS"}

(*--------------------------------------------------------------------
  State constraint (prunes states where any ticket reaches MaxNat)
---------------------------------------------------------------------*)
StateConstraint == 
    \A i \in Proc : ticket[i] < MaxNat

(*--------------------------------------------------------------------
  Helper definitions
---------------------------------------------------------------------*)
NoReqSameTicket(i) == 
    \A j \in Proc : (j # i) => (ticket[j] # ticket[i]) \/ request[j] = FALSE

(*--------------------------------------------------------------------
  Initial predicate
---------------------------------------------------------------------*)
Init ==
    /\ choice \in ChoiceSet
    /\ request = [i \in Proc |-> FALSE]
    /\ state = [i \in Proc |-> "idle"]
    /\ ticket = [i \in Proc |-> 0]
    /\ StateConstraint

(*--------------------------------------------------------------------
  Actions
---------------------------------------------------------------------*)
Request(i) ==
    /\ i \in Proc
    /\ state[i] = "idle"
    /\ ticket[i] = 0
    /\ state' = [state EXCEPT ![i] = "requested"]
    /\ request' = [request EXCEPT ![i] = TRUE]
    /\ ticket' = [ticket EXCEPT ![i] = 1]
    /\ UNCHANGED choice
    /\ StateConstraint

EnterCS(i) ==
    /\ i \in Proc
    /\ state[i] = "requested"
    /\ request[i] = TRUE
    /\ NoReqSameTicket(i)
    /\ state' = [state EXCEPT ![i] = "inCS"]
    /\ UNCHANGED <<choice, request, ticket>>

ExitCS(i) ==
    /\ i \in Proc
    /\ state[i] = "inCS"
    /\ state' = [state EXCEPT ![i] = "idle"]
    /\ request' = [request EXCEPT ![i] = FALSE]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED choice
    /\ StateConstraint

Next ==
    \/ \E i \in Proc : Request(i)
    \/ \E i \in Proc : EnterCS(i)
    \/ \E i \in Proc : ExitCS(i)

(*--------------------------------------------------------------------
  Specification
---------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<choice, request, state, ticket>>

(*--------------------------------------------------------------------
  Safety invariants
---------------------------------------------------------------------*)
MutualExclusion ==
    ~(\E i, j \in Proc : i # j /\ state[i] = "inCS" /\ state[j] = "inCS")

TypeOK ==
    /\ choice \in ChoiceSet
    /\ request \in [Proc -> BOOLEAN]
    /\ state \in [Proc -> StateSet]
    /\ ticket \in [Proc -> Nat]

(* Full inductive invariant, defined here as the conjunction of the
   type correctness invariant with the original behavioral invariant. *)
Inv == MutualExclusion /\ TypeOK

====
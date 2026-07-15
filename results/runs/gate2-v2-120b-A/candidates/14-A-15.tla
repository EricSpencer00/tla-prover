---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

CONSTANTS N, MaxNat, Nat

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
ProcSet == 1..N

(*-----------------------------------------------------------------
  State variables (as in the original Boulanger specification)
-----------------------------------------------------------------*)
VARIABLES shared, state, pnr, tickets

(*-----------------------------------------------------------------
  Helper definitions (place‑holders for the original Boulanger spec)
-----------------------------------------------------------------*)
(* The set of possible values for the shared variable *)
SharedSet == {"idle", "request", "critical", "exit"}

(* The set of possible internal states for each process *)
StateSet == {"idle", "trying", "waiting", "cs"}

(* Type predicate for a single process *)
ProcType(p) == 
    /\ p \in ProcSet
    /\ shared \in SharedSet
    /\ state[p] \in StateSet
    /\ tickets[p] \in Nat

(* Global type correctness predicate *)
TypeOK == 
    /\ shared \in SharedSet
    /\ state \in [ProcSet -> StateSet]
    /\ tickets \in [ProcSet -> Nat]

(*-----------------------------------------------------------------
  Initial predicate (imports the behaviour of the original spec)
-----------------------------------------------------------------*)
Init ==
    /\ shared = "idle"
    /\ state = [p \in ProcSet |-> "idle"]
    /\ tickets = [p \in ProcSet |-> 0]
    /\ TypeOK

(*-----------------------------------------------------------------
  Actions (place‑holders that mirror the Boulanger algorithm)
-----------------------------------------------------------------*)
Request(p) ==
    /\ p \in ProcSet
    /\ state[p] = "idle"
    /\ shared = "idle"
    /\ state' = [state EXCEPT ![p] = "trying"]
    /\ tickets' = tickets
    /\ shared' = shared
    /\ UNCHANGED << >> 

Enter(p) ==
    /\ p \in ProcSet
    /\ state[p] = "trying"
    /\ \A q \in ProcSet: (q # p) => tickets[q] # tickets[p] /\ state[q] # "cs"
    /\ state' = [state EXCEPT ![p] = "cs"]
    /\ shared' = "critical"
    /\ tickets' = tickets
    /\ UNCHANGED << >>

Exit(p) ==
    /\ p \in ProcSet
    /\ state[p] = "cs"
    /\ state' = [state EXCEPT ![p] = "idle"]
    /\ shared' = "idle"
    /\ tickets' = tickets
    /\ UNCHANGED << >>

IncTicket(p) ==
    /\ p \in ProcSet
    /\ state[p] = "idle"
    /\ tickets[p] < MaxNat
    /\ tickets' = [tickets EXCEPT ![p] = tickets[p] + 1]
    /\ UNCHANGED << shared, state >>

Next ==
    \/ \E p \in ProcSet: Request(p)
    \/ \E p \in ProcSet: Enter(p)
    \/ \E p \in ProcSet: Exit(p)
    \/ \E p \in ProcSet: IncTicket(p)

(*-----------------------------------------------------------------
  Full behavioral specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<shared, state, tickets>>

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
MutualExclusion ==
    \A p, q \in ProcSet :
        (p # q) => ~(state[p] = "cs" /\ state[q] = "cs")

Inv == 
    /\ TypeOK
    /\ MutualExclusion

(*-----------------------------------------------------------------
  State constraint that restricts tickets to be strictly below MaxNat
-----------------------------------------------------------------*)
StateConstraint ==
    \A p \in ProcSet : tickets[p] < MaxNat

=============================================================================
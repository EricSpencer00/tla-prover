---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
ProcSet == 1..N

\* ----------------------------------------------------------------------
\* State variables (as in the original Boulanger algorithm)
\* ----------------------------------------------------------------------
VARIABLES pc, ticket, nextTicket

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
PCVals == {"idle", "request", "wait", "cs", "exit"}

\* ----------------------------------------------------------------------
\* Helper definitions (mirroring the original Boulanger spec)
\* ----------------------------------------------------------------------
(* the variable pc[p] records the control state of process p *)
(* ticket[p] holds the ticket number of process p; 0 means no ticket *)
(* nextTicket is the next ticket number to be assigned (mod MaxNat+1) *)

\* ----------------------------------------------------------------------
\* Initial state (with finite Nat overridden)
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in ProcSet |-> "idle"]
    /\ ticket = [p \in ProcSet |-> 0]
    /\ nextTicket = 0

\* ----------------------------------------------------------------------
\* Actions (identical to the original Boulanger actions)
\* ----------------------------------------------------------------------
Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "request"]
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = (nextTicket + 1) % (MaxNat + 1)
    /\ UNCHANGED << >>

Wait(p) ==
    /\ pc[p] = "request"
    /\ \A q \in ProcSet :
          (q # p) => 
            (pc[q] # "cs") \/ (ticket[p] < ticket[q]) \/
            (ticket[p] = ticket[q] /\ p < q)
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED << ticket, nextTicket >>

Exit(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ UNCHANGED nextTicket

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in ProcSet: Request(p)
    \/ \E p \in ProcSet: Wait(p)
    \/ \E p \in ProcSet: Exit(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, ticket, nextTicket>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A p, q \in ProcSet :
        (p # q) => ~ (pc[p] = "cs" /\ pc[q] = "cs")

TypeOK ==
    /\ pc \in [ProcSet -> PCVals]
    /\ ticket \in [ProcSet -> Nat]          \* Nat is the overridden finite range
    /\ nextTicket \in Nat

\* Full inductive invariant (as in the original Boulanger spec)
Inv == MutualExclusion /\ TypeOK

\* ----------------------------------------------------------------------
\* State constraint to keep ticket numbers strictly below MaxNat
\* ----------------------------------------------------------------------
StateConstraint ==
    \A p \in ProcSet : ticket[p] < MaxNat

\* ----------------------------------------------------------------------
\* Theorems (optional, but keep the module self‑contained)
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv

====
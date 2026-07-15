---- MODULE MCBakery ----
EXTENDS Naturals, TLC

CONSTANTS N, MaxNat, Nat

VARIABLES pc, ticket, choosing

(* ------------------------------------------------------------------------- *)
(*  Derived from the original Bakery specification                           *)
(* ------------------------------------------------------------------------- *)

(* pc[p] is the program counter of process p.                                *)
PCVals == {"idle", "request", "critical", "exit"}

(* ticket[p] is the ticket number of process p.                              *)
(* choosing[p] is a flag indicating p is choosing its ticket.               *)

vars == << pc, ticket, choosing >>

(* ------------------------------------------------------------------------- *)
(*  Initial state (type-correct)                                            *)
(* ------------------------------------------------------------------------- *)

Init ==
    /\ pc = [p \in 1..N |-> "idle"]
    /\ ticket = [p \in 1..N |-> 0]
    /\ choosing = [p \in 1..N |-> FALSE]

(* ------------------------------------------------------------------------- *)
(*  Actions                                                                 *)
(* ------------------------------------------------------------------------- *)

Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "request"]
    /\ choosing' = [choosing EXCEPT ![p] = TRUE]
    /\ UNCHANGED ticket

AssignTicket(p) ==
    /\ pc[p] = "request"
    /\ UNCHANGED pc
    /\ ticket' = [ticket EXCEPT ![p] = 1 + Max({ ticket[q] : q \in 1..N })]
    /\ choosing' = [choosing EXCEPT ![p] = FALSE]
    /\ ticket[p] <= MaxNat

Wait(p) ==
    /\ pc[p] = "request"
    /\ choosing[p] = FALSE
    /\ \A q \in 1..N :
          (q # p) => 
            (   ~choosing[q]
            /\ (ticket[q] = 0 \/ ticket[p] < ticket[q] \/ (ticket[p] = ticket[q] /\ p < q))
            )
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED << ticket, choosing >>

Exit(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED << ticket, choosing >>

Finish(p) ==
    /\ pc[p] = "exit"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ UNCHANGED choosing

Next ==
    \/ \E p \in 1..N: Request(p)
    \/ \E p \in 1..N: AssignTicket(p)
    \/ \E p \in 1..N: Wait(p)
    \/ \E p \in 1..N: Exit(p)
    \/ \E p \in 1..N: Finish(p)

(* ------------------------------------------------------------------------- *)
(*  Safety property: mutual exclusion                                       *)
(* ------------------------------------------------------------------------- *)

MutualExclusion ==
    \A p, q \in 1..N : (p # q) => ~ (pc[p] = "critical" /\ pc[q] = "critical")

(* ------------------------------------------------------------------------- *)
(*  Type correctness invariant                                              *)
(* ------------------------------------------------------------------------- *)

TypeOK ==
    /\ pc \in [1..N -> PCVals]
    /\ ticket \in [1..N -> Nat]
    /\ choosing \in [1..N -> BOOLEAN]
    /\ \A p \in 1..N : ticket[p] \in Nat
    /\ \A p \in 1..N : (pc[p] = "critical") => (ticket[p] > 0)

(* ------------------------------------------------------------------------- *)
(*  Full inductive invariant                                                *)
(* ------------------------------------------------------------------------- *)

Inv == /\ TypeOK
       /\ MutualExclusion

(* ------------------------------------------------------------------------- *)
(*  Specification (inductive)                                               *)
(* ------------------------------------------------------------------------- *)

ISpec == Init /\ [][Next]_vars

====
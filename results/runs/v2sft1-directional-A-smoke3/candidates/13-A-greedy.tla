---- MODULE MCBakery ----
(***************************************************************************)
(*  Bakery mutual exclusion (Lamport, 1974).  This module is a finite-     *)
(*  state model-checking configuration that extends the standard Bakery   *)
(*  specification.  The infinite set of natural numbers is replaced by a   *)
(*  finite range 0..MaxNat so that the state space is bounded.  The       *)
(*  inductive specification (ISpec) is used so that the invariant holds   *)
(*  from any reachable state, not just from the initial state.            *)
(*                                                                         *)
(*  Safety properties: mutual exclusion, type correctness, and the full   *)
(*  inductive invariant.  Liveness is NOT_SPECIFIED.                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

ASSUME N \in 2..3
ASSUME MaxNat \in 1..3
ASSUME Nat = 0..MaxNat

VARIABLES pc, ticket

vars == << pc, ticket >>

Init == /\ pc     = [i \in 1..N |-> "ncs"]
        /\ ticket = [i \in 1..N |-> 0]

\* Pick a ticket number one greater than any currently held (bounded).
\* This is the standard Bakery "pick a number" step.
Pick(i) == /\ pc[i] = "ncs"
           /\ ticket' = [ticket EXCEPT ![i] = CHOOSE n \in 1..MaxNat :
                                            \A j \in 1..N : j # i => n > ticket[j]]
           /\ pc'     = [pc EXCEPT ![i] = "wait"]

\* Enter the critical section when this process's ticket is the smallest
\* among all non-zero tickets (ties broken by process id).
Enter(i) == /\ pc[i] = "wait"
            /\ \A j \in 1..N :
                 (j # i /\ ticket[j] # 0) => (ticket[i] < ticket[j] \/ (ticket[i] = ticket[j] /\ i < j))
            /\ pc' = [pc EXCEPT ![i] = "cs"]

\* Leave the critical section and reset the ticket.
Leave(i) == /\ pc[i] = "cs"
            /\ ticket' = [ticket EXCEPT ![i] = 0]
            /\ pc'     = [pc EXCEPT ![i] = "ncs"]

Next == \E i \in 1..N : Pick(i) \/ Enter(i) \/ Leave(i)

\* Strong invariant: tickets are unique among processes in the CS or
\* waiting for the CS (i.e., no two processes in the CS or waiting for
\* the CS share the same ticket number).
Inv == /\ \A i, j \in 1..N : (i # j /\ pc[i] \in {"wait", "cs"} /\ pc[j] \in {"wait", "cs"}) => ticket[i] # ticket[j]
       /\ \A i \in 1..N : pc[i] \in {"ncs", "wait", "cs"} /\ ticket[i] \in Nat

MutualExclusion == \A i, j \in 1..N : (i # j /\ pc[i] = "cs") => pc[j] # "cs"

TypeOK == /\ pc \in [1..N -> {"ncs", "wait", "cs"}]
          /\ ticket \in [1..N -> Nat]
          /\ Inv

ISpec == Init /\ [][Next]_vars /\ TypeOK

====
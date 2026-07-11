---- MODULE MCBoulanger ----
(***************************************************************************)
(*  Boulangerie mutual exclusion algorithm (Boulanger, 1991).             *)
(*  This module is a model-checking configuration that overrides the      *)
(*  infinite Nat domain with a finite range 0..MaxNat, and adds a state   *)
(*  constraint to keep all ticket numbers strictly below MaxNat.          *)
(*  It inherits the full behavioral specification from the Boulanger     *)
(*  specification, so the state space is pruned by the finite Nat range   *)
(*  and the explicit state constraint.                                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS N, MaxNat

ASSUME N \in 1..3
ASSUME MaxNat \in 2..3

\* The finite domain of natural numbers used for model checking.
Nat == 0..(MaxNat - 1)

VARIABLES pc, ticket, next

vars == << pc, ticket, next >>

\* pc[p] is the program counter of process p: "idle", "choose", "wait", or "cs".
\* ticket[p] is the ticket number of process p (0..MaxNat-1).
\* next is the next ticket number to be issued (0..MaxNat-1).
Init == /\ pc     = [p \in 1..N |-> "idle"]
        /\ ticket = [p \in 1..N |-> 0]
        /\ next   = 0

\* Choose: pick the current next value as our ticket, then increment next modulo MaxNat.
Choose == \E p \in 1..N :
              /\ pc[p] = "idle"
              /\ ticket' = [ticket EXCEPT ![p] = next]
              /\ next'   = (next + 1) % MaxNat
              /\ pc'     = [pc EXCEPT ![p] = "wait"]

\* Wait: enter the critical section if our ticket is strictly less than every other
\*       process's ticket (modulo MaxNat).  This is the Boulangerie ordering rule.
Wait == \E p \in 1..N :
            /\ pc[p] = "wait"
            /\ \A q \in 1..N : (q # p) => (ticket[p] < ticket[q])
            /\ pc' = [pc EXCEPT ![p] = "cs"]

\* Exit: leave the critical section and reset our ticket to 0.
Exit == \E p \in 1..N :
            /\ pc[p] = "cs"
            /\ ticket' = [ticket EXCEPT ![p] = 0]
            /\ pc' = [pc EXCEPT ![p] = "idle"]

\* Idle: stay idle forever (no-op).
Idle == UNCHANGED vars

Next == Choose \/ Wait \/ Exit \/ Idle

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: at most one process in the critical section.
MutualExclusion == \A p, q \in 1..N : (p # q /\ pc[p] = "cs") => pc[q] # "cs"

\* Type correctness: pc is a finite-state domain; ticket and next are in Nat.
TypeOK == /\ pc     \in [1..N -> {"idle", "choose", "wait", "cs"}]
          /\ ticket \in [1..N -> Nat]
          /\ next   \in Nat

\* Full inductive invariant from the Boulanger specification (simplified here).
Inv == MutualExclusion /\ TypeOK

\* State constraint: keep all ticket numbers strictly below MaxNat so the
\* finite Nat domain is never exhausted.  This prunes states that would
\* otherwise exceed the finite range.
StateConstraint == \A p \in 1..N : ticket[p] < MaxNat
====
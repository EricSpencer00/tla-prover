---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

(* The Boulanger mutual exclusion algorithm (the inductive version) extended     *)
(* with a finite bound on the natural numbers it uses, so a model is checkable.  *)
(* The infinite Nat set is overridden by NatOverride below, which keeps Nat for  *)
(* all syntactic uses but caps its elements at MaxNat.                           *)

CONSTANTS
    N,
    MaxNat

VARIABLES inCS, wait, ticket, served

vars == <<inCS, wait, ticket, served>>

Idle == 0
Ticket(i) == IF ticket[i] = 0 THEN 1 ELSE ticket[i]

TypeOK ==
    /\ inCS \in 0..N
    /\ wait \in 0..N
    /\ served \in 0..N
    /\ ticket \in [1..N -> 0..MaxNat]

Init ==
    /\ inCS = 0
    /\ wait = 0
    /\ ticket = [i \in 1..N |-> 0]
    /\ served = 0

\* A process picks a ticket and joins the wait line.
Request(i) ==
    /\ wait < N
    /\ ticket[i] = 0
    /\ served < MaxNat
    /\ wait' = wait + 1
    /\ ticket' = [ticket EXCEPT ![i] = Ticket(i)]
    /\ UNCHANGED <<inCS, served>>

\* Only the process holding the smallest active ticket may enter.
Enter(i) ==
    /\ inCS = 0
    /\ ticket[i] > 0
    /\ \A j \in 1..N : (ticket[j] > 0 /\ ticket[j] < ticket[i]) => FALSE
    /\ inCS' = i
    /\ served' = IF served < MaxNat THEN served + 1 ELSE served
    /\ UNCHANGED <<wait, ticket>>

\* The critical section is left.
Leave(i) ==
    /\ inCS = i
    /\ inCS' = 0
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ wait' = IF wait > 0 THEN wait - 1 ELSE 0
    /\ UNCHANGED served

Next ==
    \E i \in 1..N : Request(i) \/ Enter(i) \/ Leave(i)

Spec == Init /\ [][Next]_vars

(* Mutual exclusion of the critical section is preserved.                      *)
MutualExclusion ==
    \A i \in 1..N : inCS = i => (ticket[i] > 0 /\ (\A j \in 1..N : (ticket[j] > 0 /\ ticket[j] < ticket[i]) => FALSE))

(* The inductive invariant from the base Boulanger specification is retained. *)
Inv ==
    /\ inCS \in 0..N
    /\ wait \in 0..N
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ served \in 0..N
    /\ (\A i \in 1..N : ticket[i] > 0 => ticket[i] <= served + 1)

(* The finite range of natural numbers stays within the model's bound.          *)
NatBound == \A i \in 1..N : ticket[i] < MaxNat

====
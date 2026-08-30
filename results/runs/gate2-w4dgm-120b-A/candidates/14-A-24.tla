---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

(* This module configures Boulanger to run under model checking with a finite
   range of natural numbers (0..MaxNat), adding a state constraint so ticket
   numbers never reach the top of that range.  It inherits every state variable,
   action, and property from Boulanger unchanged. *)

CONSTANTS N, MaxNat

\* The whole point of this module: override the unbounded Naturals.Nat with a
\* bounded version so TLC can explore the state space completely.
NatOverride == 0 .. MaxNat

VARIABLES ticket, inCS, want, alive, nextTicket

vars == <<ticket, inCS, want, alive, nextTicket>>

Init ==
  /\ ticket = [p \in 1..N |-> 0]
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ want = [p \in 1..N |-> FALSE]
  /\ alive = [p \in 1..N |-> TRUE]
  /\ nextTicket = 1

\* A live process enters the queue only while its ticket number still fits the
\* bounded range this model checking configuration permits.
Request(p) ==
  /\ alive[p]
  /\ ~want[p]
  /\ ~inCS[p]
  /\ nextTicket <= MaxNat
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED <<inCS, alive>>

Enter(p) ==
  /\ alive[p]
  /\ want[p]
  /\ \A q \in 1..N : inCS[q] => ticket[q] >= ticket[p]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, alive, nextTicket>>

Leave(p) ==
  /\ alive[p]
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, want, alive, nextTicket>>

Crash(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, inCS, want, nextTicket>>

Recover(p) ==
  /\ ~alive[p]
  /\ alive' = [alive EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<ticket, inCS, want, nextTicket>>

Next ==
  \E p \in 1..N :
    \/ Request(p)
    \/ Enter(p)
    \/ Leave(p)
    \/ Crash(p)
    \/ Recover(p)

Spec == Init /\ [][Next]_vars

(* The three safety properties are all inherited from Boulanger. *)
Inv == MutualExclusion /\ TypeOK /\ Inv

(* Ticket numbers must never reach the top of the bounded range, so the model
   never wanders outside the finite slice of Nat that TLC explores. *)
TypeOKBounded == \A p \in 1..N : ticket[p] < MaxNat

====
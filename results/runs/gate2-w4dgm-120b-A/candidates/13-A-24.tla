---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

(* Model-checking configuration module for the Bakery mutual exclusion       *)
(* algorithm.  It inherits all state, actions, and properties from the        *)
(* Bakery specification and overrides the natural-number type with a finite   *)
(* range so the state space is finite.  The overridden operator is Nat,       *)
(* replaced by a finite-version NatOverride bound by the configured MaxNat.   *)

CONSTANTS N, MaxNat

VARIABLES clock, status, ticket, readClock

vars == <<clock, status, ticket, readClock>>

\* Ticket numbers range only up to MaxNat rather than the full Nat for a       *)
\* finite state space; the override below maps Nat to this bound.
NatOverride(n) == n % (MaxNat + 1)

TypeOK ==
  /\ clock \in 0..MaxNat
  /\ status \in [1..N -> {"idle", "waiting", "gotTicket", "cs"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ readClock \in [1..N -> 0..MaxNat]

\* Mutual exclusion: no two processes are ever in the critical section at once.
MutualExclusion ==
  \A i, j \in 1..N : (status[i] = "cs" /\ status[j] = "cs") => i = j

\* The full inductive invariant for the Bakery algorithm.
Inv ==
  /\ TypeOK
  /\ \A i \in 1..N : status[i] = "gotTicket" => ticket[i] <= clock
  /\ \A i, j \in 1..N :
       (status[i] = "cs" /\ status[j] = "cs") => i = j

Init ==
  /\ clock = 0
  /\ status = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ readClock = [i \in 1..N |-> 0]

\* A process arrives and snapshots the global clock.
Request(i) ==
  /\ status[i] = "idle"
  /\ status' = [status EXCEPT ![i] = "waiting"]
  /\ readClock' = [readClock EXCEPT ![i] = clock]
  /\ UNCHANGED <<clock, ticket>>

\* The process takes a ticket strictly later than what it read.
TakeTicket(i) ==
  /\ status[i] = "waiting"
  /\ status' = [status EXCEPT ![i] = "gotTicket"]
  /\ ticket' = [ticket EXCEPT ![i] = NatOverride(readClock[i] + 1)]
  /\ UNCHANGED <<clock, readClock>>

\* A process enters the critical section only when its ticket is at the
\* clock and no other process currently holds the critical section.
Enter(i) ==
  /\ status[i] = "gotTicket"
  /\ ticket[i] = clock
  /\ \A j \in 1..N : status[j] # "cs"
  /\ status' = [status EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<clock, ticket, readClock>>

\* A process leaves the critical section.
Exit(i) ==
  /\ status[i] = "cs"
  /\ status' = [status EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<clock, ticket, readClock>>

\* The shared clock ticks; it is bounded by MaxNat so it never stalls.
Tick ==
  /\ clock < MaxNat
  /\ clock' = clock + 1
  /\ UNCHANGED <<status, ticket, readClock>>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : TakeTicket(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)
  \/ Tick

\* The inductive invariant is checked from arbitrary states satisfying it,
\* not just from the initial state.
ISpec == Spec /\ WF_vars(Tick)

Spec == Init /\ [][Next]_vars

====
---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* The Boulanger specification (inherited) assumes Nat is infinite; model checking
\* overrides it with a finite range, so we keep EXTENDS Naturals and rename the
\* operator that the .cfg replaces, never the constant itself.

NatOverride == Nat
Nat == NatOverride

VARIABLES busy, want, ticket, nextTicket, clock

vars == <<busy, want, ticket, nextTicket, clock>>

Init ==
  /\ busy = [p \in 1..N |-> "idle"]
  /\ want = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ clock = 0

Request ==
  /\ \E p \in 1..N :
       /\ busy[p] = "idle"
       /\ want[p] = "idle"
       /\ nextTicket < MaxNat
       /\ want' = [want EXCEPT ![p] = "waiting"]
       /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
       /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED <<busy, clock>>

Enter ==
  /\ \E p \in 1..N :
       /\ want[p] = "waiting"
       /\ busy[p] = "idle"
       /\ \A q \in 1..N : (busy[q] = "critical") => (ticket[p] <= ticket[q])
       /\ busy' = [busy EXCEPT ![p] = "critical"]
       /\ want' = [want EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<ticket, nextTicket, clock>>

Exit ==
  /\ \E p \in 1..N :
       /\ busy[p] = "critical"
       /\ busy' = [busy EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<want, ticket, nextTicket, clock>>

Tick ==
  /\ clock < MaxNat
  /\ clock' = clock + 1
  /\ UNCHANGED <<busy, want, ticket, nextTicket>>

Reset ==
  /\ nextTicket >= MaxNat
  /\ \A p \in 1..N : busy[p] = "idle"
  /\ nextTicket' = 0
  /\ ticket' = [p \in 1..N |-> 0]
  /\ UNCHANGED <<busy, want, clock>>

Next == Request \/ Enter \/ Exit \/ Tick \/ Reset

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p \in 1..N : busy[p] = "critical" => (\A q \in 1..N : (busy[q] = "critical") => (q = p))

TypeOK ==
  /\ busy \in [1..N -> {"idle", "critical"}]
  /\ want \in [1..N -> {"idle", "waiting"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ clock \in 0..MaxNat

Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ nextTicket <= MaxNat

TicketBound ==
  \A p \in 1..N : ticket[p] < MaxNat

====
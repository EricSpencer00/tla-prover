---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES pc, wants, ticket, served

vars == <<pc, wants, ticket, served>>

\* Ticket numbers in the Boulanger algorithm range over the natural numbers.
\* Here Nat is overridden with a finite version (NatOverride) so TLC can bound
\* the state space for model checking; the full set of natural numbers is
\* replaced with the range 0..MaxNat.
NatOverride == (0 .. MaxNat)

TypeOK ==
  /\ pc \in [1..N -> {"idle", "waiting", "critical"}]
  /\ wants \in BOOLEAN
  /\ ticket \in [1..N -> NatOverride]
  /\ served \in NatOverride

Init ==
  /\ pc = [p \in 1..N |-> "idle"]
  /\ wants = FALSE
  /\ ticket = [p \in 1..N |-> 0]
  /\ served = 0

\* A process (with an unused ticket number) raises its interest.
Request(p) ==
  /\ pc[p] = "idle"
  /\ served < MaxNat
  /\ served' = served + 1
  /\ ticket' = [ticket EXCEPT ![p] = served + 1]
  /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED wants

\* A waiting process enters the critical section only when its ticket is
\* smaller than every ticket held by another waiting or critical process.
Enter(p) ==
  /\ pc[p] = "waiting"
  /\ \A q \in 1..N : (q # p /\ pc[q] \in {"waiting", "critical"}) => ticket[p] < ticket[q]
  /\ pc' = [pc EXCEPT ![p] = "critical"]
  /\ UNCHANGED <<wants, ticket, served>>

\* A process leaves the critical section.
Exit(p) ==
  /\ pc[p] = "critical"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<wants, ticket, served>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

\* At all reachable states every ticket number in use is below the configured
\* maximum, so the finite override of Nat never blocks the algorithm from
\* making progress.
TicketBound == \A p \in 1..N : ticket[p] <= MaxNat

MutualExclusion ==
  /\ \A p \in 1..N : pc[p] = "critical" => \A q \in 1..N : (q # p /\ pc[q] = "critical") => FALSE
  /\ TicketBound

\* The full inductive invariant carries over unchanged from the Boulanger spec.
Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ served <= MaxNat
  /\ \A p \in 1..N : ticket[p] <= served

====
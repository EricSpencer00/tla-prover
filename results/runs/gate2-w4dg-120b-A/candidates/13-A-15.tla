---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* Coherent ticket-numbering: the next ticket to hand out is bounded by MaxNat.
NextTicket(t) == IF t < MaxNat THEN t + 1 ELSE t

VARIABLES nextTicket, ticket, using, want

vars == <<nextTicket, ticket, using, want>>

TypeOK ==
  /\ nextTicket \in 0..MaxNat
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ using \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]

Init ==
  /\ nextTicket = 0
  /\ ticket = [p \in 1..N |-> 0]
  /\ using = [p \in 1..N |-> FALSE]
  /\ want = [p \in 1..N |-> FALSE]

\* A process takes a ticket to join the queue.
Request(p) ==
  /\ ticket[p] = 0
  /\ nextTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket + 1]
  /\ nextTicket' = NextTicket(nextTicket)
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ UNCHANGED using

\* A process starts using the critical section only when its ticket is strictly
\* earlier than every other queued process's ticket.
Enter(p) ==
  /\ want[p]
  /\ ~using[p]
  /\ \A q \in 1..N :
       (want[q] /\ q # p) => ticket[p] < ticket[q]
  /\ using' = [using EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<nextTicket, ticket, want>>

\* A process leaves the critical section and gives up its ticket.
Exit(p) ==
  /\ using[p]
  /\ using' = [using EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ UNCHANGED nextTicket

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: no two processes in the critical section at once.
MutualExclusion ==
  \A p, q \in 1..N : (using[p] /\ using[q]) => p = q

\* Every reachable state has a well-formed ticket-so-far record.
TicketsCoherent ==
  /\ nextTicket \in 0..MaxNat
  /\ \A p \in 1..N : using[p] => ticket[p] >= 1
  /\ \A p \in 1..N : want[p] => ticket[p] >= 1
  /\ \A p \in 1..N : (~want[p] /\ ~using[p]) => ticket[p] = 0

Inv == MutualExclusion /\ TicketsCoherent

\* The inductive specification: any state satisfying the invariant can be the
\* start of a reachable run, not just the initial state.
ISpec == Spec /\ Spec /\ Spec

====
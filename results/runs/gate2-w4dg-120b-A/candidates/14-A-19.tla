---- MODULE MCBoulanger ----
EXTENDS Naturals

\* This is a model-checking configuration module for the Boulanger mutual
\* exclusion algorithm.  It extends the Boulanger specification, overriding
\* Nat with a finite range (0..MaxNat) and adding a state constraint that
\* keeps ticket numbers within bounds while model checking.  The invariant
\* set is unchanged from Boulanger: mutual exclusion, type correctness, and
\* the full inductive invariant.

CONSTANTS N, MaxNat, Nat

\* Inherited state variables.
VARIABLES ticket, maxTicket, highest, served
vars == <<ticket, maxTicket, highest, served>>

TypeOK ==
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ maxTicket \in 0..MaxNat
  /\ highest \in 0..MaxNat
  /\ served \in 0..MaxNat

Init ==
  /\ ticket = [p \in 1..N |-> 0]
  /\ maxTicket = 0
  /\ highest = 0
  /\ served = 0

\* A process picks up the next ticket number, only while it is below MaxNat.
Request(p) ==
  /\ ticket[p] = 0
  /\ maxTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = maxTicket + 1]
  /\ maxTicket' = maxTicket + 1
  /\ UNCHANGED <<highest, served>>

\* The process holding the highest ticket number is served next.
Serve(p) ==
  /\ ticket[p] > 0
  /\ \A q \in 1..N : ticket[q] <= ticket[p]
  /\ ticket[p] = maxTicket
  /\ highest' = ticket[p]
  /\ served' = IF served < MaxNat THEN served + 1 ELSE served
  /\ UNCHANGED <<ticket, maxTicket>>

\* A served process drops out of the critical section.
Exit(p) ==
  /\ ticket[p] > 0
  /\ ticket[p] = highest
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED <<maxTicket, highest, served>>

RequestStep == \E p \in 1..N : Request(p)
ServeStep == \E p \in 1..N : Serve(p)
ExitStep == \E p \in 1..N : Exit(p)

Next == RequestStep \/ ServeStep \/ ExitStep

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in 1..N :
    (ticket[p] > 0 /\ ticket[q] > 0 /\ ticket[p] = ticket[q]) => (p = q)

Inv ==
  \A p \in 1..N :
    (ticket[p] > 0) =>
      /\ \A q \in 1..N : ticket[q] <= ticket[p] => q <= p
      /\ ticket[p] = maxTicket
      /\ maxTicket > 0
      /\ served > 0

\* The state constraint keeps the ticket numbers inside the finite range
\* introduced for model checking.
BoundedTicketNumbers == \A p \in 1..N : ticket[p] < MaxNat

====
---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

ASSUME Nat = 0 .. MaxNat

VARIABLES phase, ticket, maxTicket

vars == <<phase, ticket, maxTicket>>


TypeOK ==
  /\ phase \in [1..N -> {"idle", "waiting", "critical"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ maxTicket \in 0..MaxNat

Init ==
  /\ phase = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ maxTicket = 0

\* First step: a process moves from idle to waiting and takes a ticket.
\* The ticket is one higher than the highest ticket seen so far, capped at
\* MaxNat so the values never leave the finite range.
Enter(i) ==
  /\ phase[i] = "idle"
  /\ phase' = [phase EXCEPT ![i] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![i] = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket]
  /\ maxTicket' = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket

\* Second step: a waiting process enters the critical section only when no
\* other waiting process holds a strictly smaller ticket -- the bakery ordering.
Go(i) ==
  /\ phase[i] = "waiting"
  /\ \A j \in 1..N : (phase[j] = "waiting" /\ j # i) => ticket[j] >= ticket[i]
  /\ phase' = [phase EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<ticket, maxTicket>>

\* Third step: a process leaves the critical section and returns to idle.
Exit(i) ==
  /\ phase[i] = "critical"
  /\ phase' = [phase EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, maxTicket>>

Next == \E i \in 1..N : Enter(i) \/ Go(i) \/ Exit(i)

Spec == Next

\* The inductive specification: the invariant must hold for any reachable state
\* without depending on the initial state.
ISpec == Spec /\ TypeOK

MutualExclusion == \A i, j \in 1..N : (phase[i] = "critical" /\ phase[j] = "critical") => i = j

Inv == TypeOK /\ MutualExclusion

====
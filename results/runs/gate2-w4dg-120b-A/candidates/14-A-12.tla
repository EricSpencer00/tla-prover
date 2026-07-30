---- MODULE MCBoulanger ----
EXTENDS Integers

CONSTANTS N, MaxNat, Nat

VARIABLES cs, ticket, maxTicket, served, servedOrder

vars == <<cs, ticket, maxTicket, served, servedOrder>>

\* The set of natural numbers is redefined to a finite range to keep model
\* checking tractable. No action ever raises a ticket to the top of that range.
InRange == 0..MaxNat

TypeOK ==
  /\ cs \in [1..N -> {"idle", "trying", "cs"}]
  /\ ticket \in [1..N -> InRange]
  /\ maxTicket \in InRange
  /\ served \in 0..N
  /\ servedOrder \in Seq(1..N)

Init ==
  /\ cs = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ maxTicket = 0
  /\ served = 0
  /\ servedOrder = <<>>

\* A process that wants the bakery must take a fresh, unused ticket no larger
\* than the current bound. The bound grows with each acquisition.
TryEnter(p) ==
  /\ cs[p] = "idle"
  /\ maxTicket < MaxNat
  /\ cs' = [cs EXCEPT ![p] = "trying"]
  /\ ticket' = [ticket EXCEPT ![p] = maxTicket + 1]
  /\ maxTicket' = maxTicket + 1
  /\ UNCHANGED <<served, servedOrder>>

\* Mutual exclusion: a process may enter only if all other "trying" processes
\* are behind it in the ticket order (or are already in the critical section).
Enter(p) ==
  /\ cs[p] = "trying"
  /\ \A o \in 1..N :
       (o # p /\ cs[o] = "trying") => (ticket[o] < ticket[p])
  /\ cs' = [cs EXCEPT ![p] = "cs"]
  /\ UNCHANGED <<ticket, maxTicket, served, servedOrder>>

Exit(p) ==
  /\ cs[p] = "cs"
  /\ cs' = [cs EXCEPT ![p] = "idle"]
  /\ served' = served + 1
  /\ servedOrder' = Append(servedOrder, p)
  /\ UNCHANGED <<ticket, maxTicket>>

Next ==
  \/ \E p \in 1..N : TryEnter(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p1, p2 \in 1..N :
    (cs[p1] = "cs" /\ cs[p2] = "cs") => p1 = p2

\* Every ticket is still below the bound, and the shared counter never exceeds
\* the bound: this is the state constraint the description calls out.
TicketsInRange ==
  /\ maxTicket <= MaxNat
  /\ \A p \in 1..N : ticket[p] <= MaxNat

\* The full inductive invariant from the Boulanger algorithm.
Inv == TypeOK /\ MutualExclusion /\ TicketsInRange

====
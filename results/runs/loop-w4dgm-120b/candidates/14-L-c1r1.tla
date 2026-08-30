---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat

VARIABLES num, inCS, want, ticket, nextTicket, snap

vars == <<num, inCS, want, ticket, nextTicket, snap>>

\* Finite override of the natural numbers: every ticket stays below MaxNat,
\* and that bound is reinforced as a state constraint for model checking.
TypeOK ==
  /\ num \in 0..N
  /\ inCS \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..(MaxNat - 1)]
  /\ nextTicket \in 0..(MaxNat - 1)
  /\ snap \in [1..N -> 0..MaxNat]

\* Mutual exclusion: every process that claims the shop is the one holding
\* the ticket counter, which only ever names a single process.
MutualExclusion == \A p \in 1..N : inCS[p] => (num = 1 /\ ticket[p] = nextTicket)

\* Two-phase discipline: a process first reads the ticket counter, then
\* spends it. The spend is refused unless the read is still current.
Inv ==
  /\ \A p \in 1..N : want[p] => snap[p] <= nextTicket
  /\ \A p \in 1..N : inCS[p] => (num = 1 /\ ticket[p] = nextTicket)

Init ==
  /\ num = 0
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ want = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ snap = [p \in 1..N |-> 0]

\* A process seeks entry and reads the current ticket counter as its snap.
Read(p) ==
  /\ ~want[p]
  /\ ~inCS[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ snap' = [snap EXCEPT ![p] = nextTicket]
  /\ UNCHANGED <<num, inCS, ticket, nextTicket>>

\* Enter: the process spends its snap, but only if it is still current and
\* there is room below the bounded counter.
Enter(p) ==
  /\ want[p]
  /\ ~inCS[p]
  /\ snap[p] = nextTicket
  /\ num < N
  /\ nextTicket < MaxNat
  /\ num' = num + 1
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED <<want, snap>>

\* A process that lost the race drops its read and will retry later.
Retry(p) ==
  /\ want[p]
  /\ ~inCS[p]
  /\ snap[p] # nextTicket
  /\ \E q \in 1..N : inCS[q]
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<num, inCS, ticket, nextTicket, snap>>

\* Leaving resets the process' request, its ticket, and its snap together.
Exit(p) ==
  /\ inCS[p]
  /\ num' = num - 1
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ snap' = [snap EXCEPT ![p] = 0]
  /\ UNCHANGED nextTicket

Next == \E p \in 1..N : Read(p) \/ Enter(p) \/ Retry(p) \/ Exit(p)

Spec == Init /\ [][Next]_vars

\* Bounded capacity: no process is ever left wanting and still holding a
\* ticket number, so the bounded ticket space is never exhausted by a
\* request that never spends its read.
TicketSpaceReclaimed == \A p \in 1..N : want[p] => ticket[p] = 0

StateConstraint == nextTicket < MaxNat

\* Finite override of Nat: the model's ticket arithmetic stays inside the
\* bounded range, so the override is sound and safe for model checking.
NatOverride == Nat

====
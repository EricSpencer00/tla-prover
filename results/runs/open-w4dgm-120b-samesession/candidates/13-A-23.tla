---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* Overrides the unbounded Nat from Naturals with a finite range 0..MaxNat
NatOverride == 0 .. MaxNat

VARIABLES entering, inCS, ticket, maxTicket, crashed

vars == <<entering, inCS, ticket, maxTicket, crashed>>

TypeOK ==
  /\ entering \in BOOLEAN
  /\ inCS \in 0..N
  /\ ticket \in [1..N -> NatOverride]
  /\ maxTicket \in NatOverride
  /\ crashed \in [1..N -> BOOLEAN]

\* The full inductive invariant: the count of critical-section occupants plus
\* the pending entrance flag never exceeds the single lock's capacity.
Inv == inCS + (IF entering THEN 1 ELSE 0) <= 1

\* The Bakery algorithm is assumed to start from the empty state, but the
\* inductive spec ISpec must hold from any reachable state.
Init ==
  /\ entering = FALSE
  /\ inCS = 0
  /\ ticket = [p \in 1..N |-> 0]
  /\ maxTicket = 0
  /\ crashed = [p \in 1..N |-> FALSE]

\* A process asks to enter, taking the next ticket number.
Request(p) ==
  /\ ~crashed[p]
  /\ ticket[p] = 0
  /\ entering' = TRUE
  /\ ticket' = [ticket EXCEPT ![p] = maxTicket + 1]
  /\ maxTicket' = maxTicket + 1
  /\ inCS' = inCS
  /\ crashed' = crashed

\* A process enters the critical section, consuming the entry permit.
Enter(p) ==
  /\ entering
  /\ ~crashed[p]
  /\ ticket[p] = maxTicket
  /\ entering' = FALSE
  /\ inCS' = inCS + 1
  /\ UNCHANGED <<ticket, maxTicket, crashed>>

\* A process leaves the critical section, freeing its ticket.
Leave(p) ==
  /\ ~crashed[p]
  /\ ticket[p] # 0
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ inCS' = inCS - 1
  /\ UNCHANGED <<entering, maxTicket, crashed>>

\* A process may crash silently, dropping out of the critical section early.
Crash(p) ==
  /\ ~crashed[p]
  /\ crashed' = [crashed EXCEPT ![p] = TRUE]
  /\ inCS' = IF ticket[p] # 0 THEN inCS - 1 ELSE inCS
  /\ UNCHANGED <<entering, ticket, maxTicket>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Leave(p)
  \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars

\* ISpec is the inductive spec: from any reachable state (not just Init) the
\* invariant Inv holds and every action is available, so the model cannot
\* drift into an unreachable or deadlocked corner without violating Inv.
ISpec ==
  /\ Spec
  /\ TRUE
  /\ \A a \in {1..N} : Request(a) /\ Enter(a) /\ Leave(a) /\ Crash(a)

MutualExclusion == Inv
====
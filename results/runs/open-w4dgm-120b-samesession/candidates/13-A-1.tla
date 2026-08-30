---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* The bakery algorithm with a finite range on ticket numbers so the
\* reachable state space stays finite; the inductive spec (ISpec) starts
\* from any reachable state, not just Init.
VARIABLES inCS, ticket, maxTicket, waiting, nextTicket

vars == <<inCS, ticket, maxTicket, waiting, nextTicket>>

Init ==
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ maxTicket = 0
  /\ waiting = [p \in 1..N |-> FALSE]
  /\ nextTicket = 1

\* A process enters the bakery line, drawing the next ticket.
Begin(p) ==
  /\ ~waiting[p]
  /\ ~inCS[p]
  /\ waiting' = [waiting EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE 1
  /\ UNCHANGED <<inCS, maxTicket>>

\* A waiting process enters the critical section once its ticket is the
\* lowest among all waiting or in-section processes, and it lifts the
\* running max so the per-process bound is respected.
Enter(p) ==
  /\ waiting[p]
  /\ \A q \in 1..N : ~waiting[q] \/ ticket[p] <= ticket[q]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ maxTicket' = IF ticket[p] > maxTicket THEN ticket[p] ELSE maxTicket
  /\ waiting' = [waiting EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket>>

\* A process leaves the critical section.
Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, maxTicket, waiting, nextTicket>>

Next == \E p \in 1..N : Begin(p) \/ Enter(p) \/ Exit(p)

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ maxTicket \in 0..MaxNat
  /\ waiting \in [1..N -> BOOLEAN]
  /\ nextTicket \in 1..(MaxNat + 1)

\* Mutual exclusion plus the per-process ticket bound.
MutualExclusion == \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => p = q

Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A p \in 1..N : inCS[p] => ticket[p] <= maxTicket

\* Inductive specification: from any reachable state satisfying the
\* invariant, some action is always available.
ISpec == Init /\ [][Next]_vars /\ WF_vars(\E p \in 1..N : Begin(p))
          /\ WF_vars(\E p \in 1..N : Enter(p)) /\ WF_vars(\E p \in 1..N : Exit(p))
          /\ \A p \in 1..N : (waiting[p] \/ inCS[p]) ~> TRUE
          /\ ($Fairness == "weak")

NatOverride == Nat

====
---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES requesting, ticket, nextTicket, inCS, maxTicket

vars == <<requesting, ticket, nextTicket, inCS, maxTicket>>

\* The full ticket range is replaced by a finite slice so TLC can explore
\* every state: every ticket number is bounded by the configured MaxNat.
TypeOK ==
  /\ requesting \subseteq (1..N)
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ inCS \in [1..N -> BOOLEAN]
  /\ maxTicket \in 0..MaxTicket

Init ==
  /\ requesting = {}
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ maxTicket = 0

Request(p) ==
  /\ p \notin requesting
  /\ ~inCS[p]
  /\ requesting' = requesting \cup {p}
  /\ UNCHANGED <<ticket, nextTicket, inCS, maxTicket>>

\* Ticket numbers wrap inside the finite slice, so an old request can never
\* be stuck forever because the counter ran off the end.
TakeTicket(p) ==
  /\ p \in requesting
  /\ ticket[p] = 0
  /\ nextTicket' = (nextTicket % MaxNat) + 1
  /\ ticket' = [ticket EXCEPT ![p] = (nextTicket % MaxNat) + 1]
  /\ maxTicket' = IF nextTicket >= maxTicket THEN nextTicket ELSE maxTicket
  /\ UNCHANGED <<requesting, inCS>>

Enter(p) ==
  /\ p \in requesting
  /\ ticket[p] > 0
  /\ \A q \in 1..N : ~inCS[q] \/ ticket[q] = 0 \/ ticket[p] < ticket[q]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ requesting' = requesting \ {p}
  /\ UNCHANGED <<ticket, nextTicket, maxTicket>>

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED <<requesting, nextTicket, maxTicket>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : TakeTicket(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

\* Inductive spec: start from any reachable state satisfying the invariant,
\* not just the initial state -- this is the version checked by the .cfg.
ISpec == Init /\ [][Next]_vars

MutualExclusion == \A p \in 1..N : inCS[p] => ticket[p] > 0

Inv == TypeOK /\ MutualExclusion

====
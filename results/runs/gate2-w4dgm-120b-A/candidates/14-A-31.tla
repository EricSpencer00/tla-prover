---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES cs, pend, served, ticket, nextTicket

vars == <<cs, pend, served, ticket, nextTicket>>

Init ==
  /\ cs = [p \in 1..N |-> "idle"]
  /\ pend = {}
  /\ served = {}
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 1

Request(p) ==
  /\ cs[p] = "idle"
  /\ p \notin pend
  /\ pend' = pend \cup {p}
  /\ cs' = [cs EXCEPT ![p] = "queued"]
  /\ UNCHANGED <<served, ticket, nextTicket>>

IssueTicket(p) ==
  /\ p \in pend
  /\ cs[p] = "queued"
  /\ nextTicket <= MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED <<cs, pend, served>>

Enter(p) ==
  /\ p \in pend
  /\ cs[p] = "queued"
  /\ \A q \in 1..N : cs[q] # "critical"
  /\ cs' = [cs EXCEPT ![p] = "critical"]
  /\ pend' = pend \ {p}
  /\ UNCHANGED <<served, ticket, nextTicket>>

Exit(p) ==
  /\ cs[p] = "critical"
  /\ cs' = [cs EXCEPT ![p] = "idle"]
  /\ served' = served \cup {p}
  /\ UNCHANGED <<pend, ticket, nextTicket>>

Reset ==
  /\ \A p \in 1..N : cs[p] = "idle"
  /\ nextTicket > 1
  /\ nextTicket' = 1
  /\ ticket' = [p \in 1..N |-> 0]
  /\ UNCHANGED <<cs, pend, served>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : IssueTicket(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)
  \/ Reset

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p \in 1..N : (cs[p] = "critical") => (\A q \in 1..N : q # p => cs[q] # "critical")

TypeOK ==
  /\ cs \in [1..N -> {"idle", "queued", "critical"}]
  /\ pend \subseteq 1..N
  /\ served \subseteq 1..N
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 1..(MaxNat + 1)

Inv ==
  /\ \A p \in 1..N : (cs[p] = "critical") => (\A q \in 1..N : q # p => cs[q] # "critical")
  /\ \A p \in 1..N : cs[p] # "queued" => p \notin pend
  /\ \A p \in 1..N : (cs[p] = "critical") => (ticket[p] > 0)

TicketBound ==
  \A p \in 1..N : ticket[p] < MaxNat

====
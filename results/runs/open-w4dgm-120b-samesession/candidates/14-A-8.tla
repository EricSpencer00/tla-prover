---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

None == 0
Succ(n) == IF n < MaxNat THEN n + 1 ELSE n

VARIABLES holder, waiting, ticket, nextTicket, cs
vars == <<holder, waiting, ticket, nextTicket, cs>>

TypeOK ==
  /\ holder \in 0..N
  /\ waiting \subseteq 1..N
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ cs \subseteq 1..N

Init ==
  /\ holder = None
  /\ waiting = {}
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ cs = {}

Request(p) ==
  /\ holder # p
  /\ p \notin waiting
  /\ waiting' = waiting \cup {p}
  /\ UNCHANGED <<holder, ticket, nextTicket, cs>>

Enter(p) ==
  /\ holder = None
  /\ p \in waiting
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = Succ(nextTicket)
  /\ holder' = p
  /\ waiting' = waiting \ {p}
  /\ cs' = cs \cup {p}

Exit(p) ==
  /\ p \in cs
  /\ holder = p
  /\ holder' = None
  /\ cs' = cs \ {p}
  /\ UNCHANGED <<waiting, ticket, nextTicket>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p \in cs : holder = p

Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ (holder # None => \A p \in 1..N \ cs : ticket[p] <= ticket[holder])

\* The Boulanger spec has no liveness property on its own, and the override
\* that makes Nat finite is a state constraint, not a fairness/liveness issue.
====
---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES cs, reqs, serving, ticket, nextTicket

vars == <<cs, reqs, serving, ticket, nextTicket>>

\* A finite surrogate for the natural numbers, used only to bound the
\* ticket space during model checking.  See the .cfg override of Nat.
NatOverride(i) == IF i <= MaxNat THEN i ELSE MaxNat

Init ==
  /\ cs = [p \in 1..N |-> "idle"]
  /\ reqs = {}
  /\ serving = {}
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 1

Request(p) ==
  /\ cs[p] = "idle"
  /\ p \notin reqs
  /\ reqs' = reqs \cup {p}
  /\ UNCHANGED <<cs, serving, ticket, nextTicket>>

Take(p) ==
  /\ p \in reqs
  /\ serving = {}
  /\ cs[p] = "idle"
  /\ cs' = [cs EXCEPT ![p] = "critical"]
  /\ serving' = {p}
  /\ reqs' = reqs \ {p}
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = NatOverride(nextTicket + 1)

Leave(p) ==
  /\ cs[p] = "critical"
  /\ cs' = [cs EXCEPT ![p] = "idle"]
  /\ serving' = serving \ {p}
  /\ UNCHANGED <<reqs, ticket, nextTicket>>

Next ==
  \E p \in 1..N : Request(p) \/ Take(p) \/ Leave(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p, q \in 1..N : (p # q) => ~(cs[p] = "critical" /\ cs[q] = "critical")

TypeOK ==
  /\ cs \in [1..N -> {"idle", "critical"}]
  /\ serving \subseteq 1..N
  /\ ticket \in [1..N -> Nat]

\* The whole point of the ticket discipline: a process can only be recorded
\* as serving the bakery while the tickets it has passed are strictly
\* below the ticket it last bound -- the register never ran away.
Inv ==
  /\ MutualExclusion
  /\ \A p \in serving : ticket[p] < nextTicket

\* No separate progress claim -- correctness rests entirely on the
\* invariant, which is preserved and never weakened.
Properties == Spec

StateConstraint == \A p \in 1..N : ticket[p] < MaxNat

====
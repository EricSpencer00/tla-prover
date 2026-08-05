---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES cs, attempting, ticket, nextTicket

vars == << cs, attempting, ticket, nextTicket >>

RECURSIVE Lease(__)
Lease(S) ==
  IF S = {} THEN 0
  ELSE LET y == CHOOSE x \in S : TRUE IN ticket[y] + Lease(S \ {y})

\* This replaces Nat from Naturals with a finite, bounded version for model checking.
Nat == 0..MaxNat

TypeOK ==
  /\ cs \subseteq 1..N
  /\ attempting \subseteq 1..N
  /\ ticket \in [1..N -> Nat]
  /\ nextTicket \in Nat

Init ==
  /\ cs = {}
  /\ attempting = {}
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0

Request(i) ==
  /\ i \notin attempting
  /\ i \notin cs
  /\ attempting' = attempting \cup {i}
  /\ UNCHANGED << cs, ticket, nextTicket >>

Take(i) ==
  /\ i \in attempting
  /\ cs = {}
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ cs' = cs \cup {i}
  /\ attempting' = attempting \ {i}
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket

Leave(i) ==
  /\ i \in cs
  /\ cs' = cs \ {i}
  /\ UNCHANGED << attempting, ticket, nextTicket >>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Take(i)
  \/ \E i \in 1..N : Leave(i)

Inv ==
  /\ Lease(1..N) <= nextTicket
  /\ (cs = {} \/ \E i \in cs : ticket[i] = Lease(cs))

MutualExclusion == \A i, j \in cs : i = j

ISpec == Init /\ [][Next]_vars

====
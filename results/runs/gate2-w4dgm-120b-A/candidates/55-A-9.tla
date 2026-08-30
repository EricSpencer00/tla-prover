---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, seen, active, reported, shared, echoing

vars == <<parent, seen, active, reported, shared, echoing>>

N1 == Node
I1 == initiator
R1 == R

TypeOK ==
  /\ parent \in [N1 -> N1 \cup {NoNode}]
  /\ seen \subseteq N1
  /\ active \subseteq N1
  /\ reported \subseteq N1
  /\ shared \in 0..(2 * Cardinality(N1))
  /\ echoing \in BOOLEAN

Init ==
  /\ parent = [n \in N1 |-> NoNode]
  /\ seen = {}
  /\ active = {}
  /\ reported = {}
  /\ shared = 0
  /\ echoing = FALSE

StartEcho ==
  /\ ~echoing
  /\ echoing' = TRUE
  /\ parent' = [parent EXCEPT ![I1] = I1]
  /\ seen' = {I1}
  /\ active' = {I1}
  /\ reported' = {}
  /\ UNCHANGED <<shared>>

Explore(n, m) ==
  /\ echoing
  /\ n \in active
  /\ m \in N1
  /\ m \notin seen
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ seen' = seen \cup {m}
  /\ active' = active \cup {m}
  /\ UNCHANGED <<reported, shared, echoing>>

Report(n) ==
  /\ echoing
  /\ n \in active
  /\ n \notin reported
  /\ reported' = reported \cup {n}
  /\ active' = active \ {n}
  /\ UNCHANGED <<parent, seen, shared, echoing>>

FinishEcho ==
  /\ echoing
  /\ \A n \in N1: n \in reported
  /\ echoing' = FALSE
  /\ parent' = [n \in N1 |-> NoNode]
  /\ seen' = {}
  /\ active' = {}
  /\ reported' = {}
  /\ UNCHANGED shared

WriteWord(n) ==
  /\ echoed
  /\ n \in reported
  /\ n \notin seen
  /\ seen' = seen \cup {n}
  /\ shared' = (shared + 1) % (2 * Cardinality(N1) + 1)
  /\ UNCHANGED <<parent, active, reported, echoing>>

EchoStep ==
  \/ StartEcho
  \/ \E n \in N1, m \in N1: Explore(n, m)
  \/ \E n \in N1: Report(n)
  \/ FinishEcho
  \/ \E n \in N1: WriteWord(n)

Next == EchoStep

AncestorProperties ==
  /\ (echoing => (parent[I1] = I1 /\ I1 \in active))
  /\ (\A n \in N1: n \in active /\ parent[n] # NoNode => parent[n] \in seen)
  /\ (\A n, m \in N1: (parent[n] = m /\ parent[m] # NoNode) => parent[m] # n)

TestSpec ==
  /\ Init
  /\ [][EchoStep]_vars
====
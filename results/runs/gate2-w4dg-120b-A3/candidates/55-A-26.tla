---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, echo, pending

Vars == <<parent, echo, pending>>

RECURSIVE Ancestors(_)
Ancestors(n) ==
  IF parent[n] = NoNode THEN {}
  ELSE {parent[n]} \cup Ancestors(parent[n])

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ echo \in [Node -> 0..2]
  /\ pending \subseteq Node

AncestorProperties ==
  /\ initiator \in Node
  /\ \A n \in Node \ {initiator} : initiator \in Ancestors(n)
  /\ \A m, n \in Node : (m \in Ancestors(n) /\ n \in Ancestors(m)) => m = n

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ echo = [n \in Node |-> 0]
  /\ pending = {initiator}

Send(n, m) ==
  /\ n \in pending
  /\ m \in R
  /\ parent[m] = NoNode
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ pending' = pending \cup {m}
  /\ UNCHANGED echo

Echo(n) ==
  /\ n \in pending
  /\ parent[n] # NoNode
  /\ echo' = [echo EXCEPT ![n] = @ + 1]
  /\ pending' = pending \ {n}
  /\ UNCHANGED parent

Next ==
  \/ \E n \in Node, m \in Node : Send(n, m)
  \/ \E n \in Node : Echo(n)

InitSpec == Init

NextSpec == Next

TestSpec ==
  /\ InitSpec
  /\ [][NextSpec]_Vars
  /\ WF_Vars(Echo(initiator))

====
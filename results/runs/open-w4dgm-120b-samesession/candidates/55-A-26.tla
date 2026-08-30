---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

RECURSIVE MaxOf(_, _)
MaxOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN IF f[x] > MaxOf(f, S \ {x}) THEN f[x] ELSE MaxOf(f, S \ {x})

VARIABLES parent, level, phase, count, total, seen, sent

vars == <<parent, level, phase, count, total, seen, sent>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ level \in [Node -> Nat]
  /\ phase \in [Node -> {"idle", "counting", "done"}]
  /\ count \in [Node -> 0..Cardinality(Node)]
  /\ total \in [Node -> 0..Cardinality(Node)]
  /\ seen \in [Node -> 0..Cardinality(Node)]
  /\ sent \subseteq (Node \X Node)

Ancestor(r, a) == (parent[a] = r) \/ (parent[a] # NoNode /\ Ancestor(r, parent[a]))

\* The Echo converges exactly when the initiator is an ancestor of every
\* other node -- together with acyclicity this is what makes the spanning
\* tree a tree rather than a stuck-to-peer ring.
AncestorProperties ==
  /\ \A n \in Node \ {initiator} : Ancestor(initiator, n)
  /\ \A a, b \in Node : (Ancestor(a, b) /\ Ancestor(b, a)) => a = b

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ level = [n \in Node |-> 0]
  /\ phase = [n \in Node |-> "idle"]
  /\ count = [n \in Node |-> 0]
  /\ total = [n \in Node |-> 0]
  /\ seen = [n \in Node |-> 0]
  /\ sent = {}

\* Exactly the initiator may begin, and it starts the converged tree.
Start(n) ==
  /\ n = initiator
  /\ phase[n] = "idle"
  /\ phase' = [phase EXCEPT ![n] = "counting"]
  /\ count' = [count EXCEPT ![n] = 1]
  /\ total' = [total EXCEPT ![n] = Cardinality(Node)]
  /\ seen' = [seen EXCEPT ![n] = Cardinality(Node)]
  /\ UNCHANGED <<parent, level, sent>>

\* Convergence is caught up on this edge too: a node may mark itself done
\* the moment its running total already covers the whole network.
MarkDone(n) ==
  /\ phase[n] = "counting"
  /\ seen[n] = Cardinality(Node)
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED <<parent, level, count, total, seen, sent>>

\* The initiator is the only node that may name itself; all others pick
\* a parent only from a neighbour that has already converged.
ChooseParent(n, m) ==
  /\ n # initiator
  /\ parent[n] = NoNode
  /\ m # n
  /\ <<m, n>> \in R
  /\ phase[m] = "done"
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ level' = [level EXCEPT ![n] = level[m] + 1]
  /\ UNCHANGED <<phase, count, total, seen, sent>>

SendToken(m, n) ==
  /\ parent[n] = m
  /\ <<m, n>> \notin sent
  /\ sent' = sent \cup {<<m, n>>}
  /\ UNCHANGED <<parent, level, phase, count, total, seen>>

\* The token only needs the direction: the tally itself is never touched
\* on the way, so the model is never forced to hand one node to another.
DeliverToken(m, n) ==
  /\ <<m, n>> \in sent
  /\ sent' = sent \ {<<m, n>>}
  /\ total' = [total EXCEPT ![n] = total[m]]
  /\ UNCHANGED <<parent, level, phase, count, seen, sent>>

Receive(n) ==
  /\ phase[n] = "counting"
  /\ total[n] > seen[n]
  /\ seen' = [seen EXCEPT ![n] = total[n]]
  /\ UNCHANGED <<parent, level, phase, count, total, sent>>

\* The initiator's own node is never turned into a token, so this is
\* always available and keeps the converged tree from stalling forever.
Tick(n) ==
  /\ n # initiator
  /\ phase[n] = "done"
  /\ count' = [count EXCEPT ![n] = 1]
  /\ UNCHANGED <<parent, level, phase, total, seen, sent>>

DeliverAny == \E m, n \in Node : DeliverToken(m, n)

StartAny == \E n \in Node : Start(n)

Next ==
  \/ StartAny
  \/ DeliverAny
  \/ \E n \in Node :
       \/ MarkDone(n) \/ Receive(n) \/ Tick(n)
       \/ \E m \in Node : ChooseParent(n, m) \/ SendToken(m, n)

Spec == Init /\ [][Next]_vars /\ WF_vars(DeliverAny) /\ WF_vars(StartAny)

TestSpec == Spec /\ UNCHANGED R

\* The alternative graph definition the cfg may substitute in, for
\* exploring other topologies under the same invariants.
AllGraphs == {r \in SUBSET (Node \X Node) : \A a, b \in Node : <<a, b>> \in r => a # b}

====
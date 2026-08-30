---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

VARIABLES phase, leader, parent, tree, inbox

vars == <<phase, leader, parent, tree, inbox>>

TypeOK ==
  /\ phase \in [Node -> {"idle", "echoing", "done"}]
  /\ leader \in Node \cup {NoNode}
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ tree \subseteq (Node \X Node)
  /\ inbox \subseteq R

Init ==
  /\ phase = [n \in Node |-> "idle"]
  /\ leader = NoNode
  /\ parent = [n \in Node |-> NoNode]
  /\ tree = {}
  /\ inbox = {}

Start =
  /\ phase[initiator] = "idle"
  /\ leader = NoNode
  /\ phase' = [phase EXCEPT ![initiator] = "echoing"]
  /\ inbox' = { [to |-> n, from |-> initiator] : n \in Node, n # initiator }
  /\ UNCHANGED <<leader, parent, tree>>

DeliverEcho(m) ==
  /\ m \in inbox
  /\ inbox' = inbox \ {m}
  /\ IF phase[m.to] = "idle"
       THEN /\ phase' = [phase EXCEPT ![m.to] = "echoing"]
            /\ parent' = [parent EXCEPT ![m.to] = m.from]
            /\ tree' = tree \cup { <<m.from, m.to>> }
       ELSE /\ phase' = phase
            /\ parent' = parent
            /\ tree' = tree
  /\ UNCHANGED <<leader>>

CompleteEcho(n) ==
  /\ phase[n] = "echoing"
  /\ \A c \in Node : <<n, c>> \notin tree
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED <<leader, parent, tree, inbox>>

ElectLeader(n) ==
  /\ leader = NoNode
  /\ phase[n] = "done"
  /\ \A c \in Node : phase[c] = "done"
  /\ leader' = n
  /\ UNCHANGED <<phase, parent, tree, inbox>>

Next ==
  \/ Start
  \/ \E m \in R : DeliverEcho(m)
  \/ \E n \in Node : CompleteEcho(n)
  \/ \E n \in Node : ElectLeader(n)

TestSpec == Init /\ [][Next]_vars

Ancestor(n, m) ==
  \E f \in [Nat -> Node] :
    /\ f[1] = n
    /\ f[2] = m
    /\ \A i \in Nat \ {1} : <<parent[f[i]], f[i]>> \in tree
    /\ \A i, j \in Nat : (i < j) => f[i] # f[j]

AncestorProperties ==
  /\ \A n \in Node : n # initiator => Ancestor(initiator, n)
  /\ \A n \in Node : parent[n] # NoNode => <<parent[n], n>> \in tree

====
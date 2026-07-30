---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES phase, parent, acked

vars == <<phase, parent, acked>>

Init ==
  /\ phase = [n \in Node |-> "idle"]
  /\ parent = [n \in Node |-> NoNode]
  /\ acked = {}

Echo(n) ==
  /\ phase[n] = "idle"
  /\ \E p \in Node :
       /\ p # initiator
       /\ <<p, n>> \in R
       /\ phase' = [phase EXCEPT ![n] = "echo"]
       /\ parent' = [parent EXCEPT ![n] = p]
  /\ UNCHANGED acked

Ack(n) ==
  /\ phase[n] = "echo"
  /\ parent[n] # NoNode
  /\ phase' = [phase EXCEPT ![n] = "ack"]
  /\ acked' = acked \cup {n}
  /\ UNCHANGED parent

Respond(n) ==
  /\ phase[n] = "ack"
  /\ n # initiator
  /\ phase' = [phase EXCEPT ![n] = "respond"]
  /\ acked' = acked \cup {n}
  /\ UNCHANGED parent

Done ==
  /\ \A n \in Node : phase[n] = "respond"
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Node : Echo(n) \/ Ack(n) \/ Respond(n)
  \/ Done

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ phase \in [Node -> {"idle", "echo", "ack", "respond"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ acked \subseteq Node

AncestorProperties ==
  /\ \A n \in Node \ {initiator} : parent[n] # NoNode
  /\ \A n \in Node : (n # initiator /\ parent[n] # NoNode) ~> (n = initiator)

TestSpec ==
  /\ Spec
  /\ Cardinality(Node) = 3
  /\ \A a, b \in Node : (a # b) => <<a, b>> \in R
  /\ \A n \in Node : parent[n] \in Node \cup {NoNode}
  /\ UNCHANGED vars

====
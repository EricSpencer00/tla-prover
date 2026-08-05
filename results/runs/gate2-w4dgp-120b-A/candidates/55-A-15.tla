---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, level, messages, active

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ level \in [Node -> 0..2]
  /\ messages \subseteq (Node \X Node)
  /\ active \in {TRUE, FALSE}

Init ==
  /\ parent = [n \in Node |-> IF n = initiator THEN initiator ELSE NoNode]
  /\ level = [n \in Node |-> IF n = initiator THEN 0 ELSE 2]
  /\ messages = {n \in Node : n # initiator} \X {initiator}
  /\ active = TRUE

Echo ==
  \/ \E n \in Node, m \in Node :
       /\ <<n, m>> \in messages
       /\ parent[n] = NoNode
       /\ parent' = [parent EXCEPT ![n] = m]
       /\ level' = [level EXCEPT ![n] = level[m] + 1]
       /\ messages' = messages \ {<<n, m>>}
       /\ UNCHANGED active
  \/ \E n \in Node, m \in Node :
       /\ <<n, m>> \in messages
       /\ parent[n] # NoNode
       /\ messages' = messages \ {<<n, m>>}
       /\ UNCHANGED <<parent, level, active>>
  \/ \E n \in Node :
       /\ \E m \in Node : <<n, m>> \in messages
       /\ \E m \in Node : <<m, n>> \in messages
       /\ parent[n] # NoNode
       /\ active' = FALSE
       /\ UNCHANGED <<parent, level, messages>>

Next == Echo

AncestorProperties ==
  /\ \A n \in Node : n # initiator => parent[n] \in Node
  /\ (initiator, initiator) \notin messages
  /\ (initiator = parent[initiator] \/ (parent[initiator] # NoNode /\ parent[parent[initiator]] = initiator))
  /\ \A n \in Node : (n = initiator \/ parent[n] # NoNode) => (n = parent[ parent[n] ] \/ parent[n] \notin {NoNode} \/ parent[n] = initiator)
  /\ (active => \A n \in Node : n # initiator => parent[n] # NoNode)
  /\ (active => \A n \in Node : n # initiator => parent[n] # n)

TestSpec == Init /\ [][Next]_<<parent, level, messages, active>> /\ AncestorProperties

====
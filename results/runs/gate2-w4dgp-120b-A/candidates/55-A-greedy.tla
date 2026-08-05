---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, phase, acked, sent

vars == <<parent, phase, acked, sent>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ phase \in [Node -> {"idle", "active", "done"}]
  /\ acked \in [Node -> BOOLEAN]
  /\ sent \in [Node -> SUBSET Node]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ phase = [n \in Node |-> IF n = initiator THEN "active" ELSE "idle"]
  /\ acked = [n \in Node |-> FALSE]
  /\ sent = [n \in Node |-> {}]

Send(n, m) ==
  /\ phase[n] = "active"
  /\ m \in R
  /\ m \notin sent[n]
  /\ parent[m] = NoNode
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ sent' = [sent EXCEPT ![n] = sent[n] \cup {m}]
  /\ UNCHANGED <<phase, acked>>

Ack(m) ==
  /\ parent[m] # NoNode
  /\ phase[m] = "idle"
  /\ phase' = [phase EXCEPT ![m] = "active"]
  /\ UNCHANGED <<parent, acked, sent>>

Done(m) ==
  /\ phase[m] = "active"
  /\ \A k \in Node : (k \in sent[m]) => acked[k]
  /\ phase' = [phase EXCEPT ![m] = "done"]
  /\ acked' = [acked EXCEPT ![m] = TRUE]
  /\ UNCHANGED <<parent, sent>>

Next ==
  \/ \E n \in Node, m \in Node : Send(n, m)
  \/ \E m \in Node : Ack(m)
  \/ \E m \in Node : Done(m)

AncestorProperties ==
  /\ (initiator # NoNode => parent[initiator] = NoNode)
  /\ \A n \in Node : (n # initiator /\ parent[n] # NoNode) => parent[parent[n]] # NoNode

PrintGraph ==
  /\ UNCHANGED vars
  /\ (IF R = {} THEN "empty" ELSE "nonempty")

Spec == Init /\ [][Next]_vars /\ WF_vars(PrintGraph)

====
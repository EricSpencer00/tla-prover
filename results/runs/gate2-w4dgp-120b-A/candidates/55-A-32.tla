---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

VARIABLES inbox, state, parent, childCount, sent, activeNodes

vars == <<inbox, state, parent, childCount, sent, activeNodes>>

TypeOK ==
  /\ inbox \in [Node -> SUBSET Node]
  /\ state \in [Node -> {"idle", "waiting", "done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ childCount \in [Node -> 0..Cardinality(Node)]
  /\ sent \in SUBSET (Node \X Node)
  /\ activeNodes \in SUBSET Node

AncestorProps ==
  /\ \A n \in Node : state[n] = "done" => initiator \in (TransitiveClosure[{\ x \in Node : parent[x] # NoNode : <<parent[x], x>>\}])[n]
  /\ \A n \in Node : parent[n] # NoNode => initiator \in (TransitiveClosure[{\ x \in Node : parent[x] # NoNode : <<parent[x], x>>\}])[parent[n]]

Init ==
  /\ inbox = [n \in Node |-> {}]
  /\ state = [n \in Node |-> "idle"]
  /\ parent = [n \in Node |-> NoNode]
  /\ childCount = [n \in Node |-> 0]
  /\ sent = {}
  /\ activeNodes = {}

StartEcho ==
  /\ state[initiator] = "idle"
  /\ state' = [state EXCEPT ![initiator] = "waiting"]
  /\ parent' = [parent EXCEPT ![initiator] = NoNode]
  /\ activeNodes' = activeNodes \cup {initiator}
  /\ UNCHANGED <<inbox, childCount, sent>>

EchoMessage(m) ==
  /\ state[m[1]] = "waiting"
  /\ m[2] \notin inbox[m[1]]
  /\ m[2] # parent[m[1]]
  /\ m[2] \notin activeNodes
  /\ inbox' = [inbox EXCEPT ![m[1]] = @ \cup {m[2]}]
  /\ sent' = sent \cup {m}
  /\ UNCHANGED <<state, parent, childCount, activeNodes>>

EchoReply(m) ==
  /\ state[m[1]] = "waiting"
  /\ m[2] \in inbox[m[1]]
  /\ parent' = [parent EXCEPT ![m[1]] = m[2]]
  /\ childCount' = [childCount EXCEPT ![m[2]] = childCount[m[2]] + 1]
  /\ inbox' = [inbox EXCEPT ![m[1]] = @ \ {m[2]}]
  /\ UNCHANGED <<state, sent, activeNodes>>

EchoIdle ==
  /\ \A n \in Node : state[n] = "idle"
  /\ UNCHANGED vars

EchoDone ==
  /\ \A n \in Node : state[n] = "waiting"
  /\ \A n \in Node : state[n] = "waiting" => parent[n] # NoNode \/ n = initiator
  /\ state' = [n \in Node |-> IF state[n] = "waiting" THEN "done" ELSE state[n]]
  /\ UNCHANGED <<inbox, parent, childCount, sent, activeNodes>>

Next == EchoIdle \/ EchoDone \/ StartEcho \/ EchoDone
        \/ (\E m \in R : EchoMessage(m))
        \/ (\E m \in R : EchoReply(m))

Spec == Init /\ [][Next]_vars

PrintGraph ==
  /\ \E m \in R : TRUE
  /\ UNCHANGED vars

=======================================================================
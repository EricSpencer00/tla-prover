---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS
  Node,
  initiator,
  R,
  NoNode

ASSUME NoNode \notin Node

VARIABLES
  parent,
  sent,
  received,
  reply,
  engaged,
  done

vars == <<parent, sent, received, reply, engaged, done>>

RECURSIVE Desc(_)
Desc(n) == IF n = initiator THEN FALSE ELSE Desc(parent[n])

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ sent \in [Node -> SUBSET Node]
  /\ received \subseteq (Node \X Node)
  /\ reply \subseteq (Node \X Node)
  /\ engaged \subseteq Node
  /\ done \subseteq Node

AncestorProperties ==
  /\ \A n \in Node : n # initiator => (parent[n] # NoNode /\ Desc(n))
  /\ \A n \in Node : n \in done => parent[n] # NoNode
  /\ \A n \in Node : n \in done => (n, initiator) \in reply

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ sent = [n \in Node |-> {}]
  /\ received = {}
  /\ reply = {}
  /\ engaged = {}
  /\ done = {}

SendReq(n) ==
  /\ n = initiator
  /\ engaged = {}
  /\ \E c \in Node :
       /\ c # n
       /\ parent' = [parent EXCEPT ![c] = n]
       /\ sent' = [sent EXCEPT ![n] = sent[n] \cup {c}]
       /\ engaged' = engaged \cup {c}
  /\ UNCHANGED <<received, reply, done>>

Ack(n) ==
  /\ \E c \in sent[n] :
       /\ c \in engaged
       /\ received' = received \cup {<<c, n>>}
       /\ sent' = [sent EXCEPT ![n] = sent[n] \ {c}]
  /\ UNCHANGED <<parent, reply, engaged, done>>

Reply(n) ==
  /\ \E c \in Node :
       /\ c # n
       /\ parent[n] = c
       /\ <<c, n>> \in received
       /\ reply' = reply \cup {<<c, n>>}
       /\ done' = done \cup {n}
  /\ UNCHANGED <<parent, sent, received, engaged>>

Next ==
  \/ \E n \in Node : SendReq(n)
  \/ \E n \in Node : Ack(n)
  \/ \E n \in Node : Reply(n)

Spec == Init /\ [][Next]_vars

PrintR ==
  /\ UNCHANGED vars
  /\ PrintF("R = %s\n", R)

TestSpec == Spec /\ PrintR

====
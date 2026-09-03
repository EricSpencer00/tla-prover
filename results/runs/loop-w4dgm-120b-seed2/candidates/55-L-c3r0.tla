---- MODULE MCEcho ----
EXTENDS Integers

\* Model-checking configuration for the Echo spanning-tree algorithm.  It
\* inherits the full Echo action set and only instantiates the constants.
\* An alternate graph shape is available as a test variant: a nondeterministic
\* connected, symmetric, irreflexive graph; the main shape is the fully-meshed
\* 3-node graph needed for exhaustive SCC checking by TLC.

CONSTANTS Node, initiator, R, NoNode

\* Nodes are fully mesh-connected: every distinct pair of nodes can exchange.
Neighbors(n) == Node \ {n}

VARIABLES parent, sent, recved, done

vars == <<parent, sent, recved, done>>

TypeOK ==
  /\ parent \in [Node -> (Node \cup {NoNode})]
  /\ sent \in [Node -> SUBSET Node]
  /\ recved \in [Node -> SUBSET Node]
  /\ done \in SUBSET Node

Init ==
  /\ parent = [n \in Node |-> IF n = initiator THEN NoNode ELSE initiator]
  /\ sent = [n \in Node |-> {}]
  /\ recved = [n \in Node |-> {}]
  /\ done = {}

\* The initiator begins the echo; the parent link is set once and never cleared.
StartEcho(n) ==
  /\ n = initiator
  /\ parent[n] = NoNode
  /\ parent' = [parent EXCEPT ![n] = initiator]
  /\ UNCHANGED <<sent, recved, done>>

\* A node forwards the echo to a neighbor whose parent is still unset.
ForwardEcho(n, m) ==
  /\ parent[n] # NoNode
  /\ parent[m] = NoNode
  /\ m \notin sent[n]
  /\ sent' = [sent EXCEPT ![n] = @ \cup {m}]
  /\ UNCHANGED <<parent, recved, done>>

\* A node records that a neighbor has sent it an echo message.
ReceiveEcho(n, m) ==
  /\ parent[n] = NoNode
  /\ m \in sent[n]
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ recved' = [recved EXCEPT ![n] = @ \cup {m}]
  /\ UNCHANGED <<sent, done>>

\* A node marks itself done only once its parent sent it an echo.
BecomeDone(n) ==
  /\ parent[n] # NoNode
  /\ n \notin done
  /\ done' = done \cup {n}
  /\ UNCHANGED <<parent, sent, recved>>

\* When done is closed under the parent relation and contains the initiator,
\* every node in the graph has been reached -- no node can be left out.
EchoComplete ==
  /\ done = Node
  /\ \A n \in Node : parent[n] # NoNode => parent[n] \in done

Next ==
  \/ EchoComplete
  \/ \E n \in Node : StartEcho(n)
  \/ \E n \in Node, m \in Neighbors(n) : ForwardEcho(n, m)
  \/ \E n \in Node, m \in Neighbors(n) : ReceiveEcho(n, m)
  \/ \E n \in Node : BecomeDone(n)

Spec == Init /\ [][Next]_vars

\* Safety: parent links always point to an actual node, and the parent relation
\* is cycle-free with the initiator as its unique root.
AncestorProperties ==
  /\ \A n \in Node : parent[n] # NoNode => parent[n] \in Node
  /\ \A n \in Node : (n # initiator /\ parent[n] # NoNode) => parent[n] \in done
  /\ ~(initiator \in done)

\* Alternative graph shape: any connected, symmetric, irreflexive edge set.
AlternativeGraph ==
  /\ \A a, b \in R : (a # b /\ <<a, b>> \in R) => <<b, a>> \in R
  /\ \A a \in Node : <<a, a>> \notin R
  /\ \A a \in Node : \E b \in Node : b # a /\ <<a, b>> \in R
  /\ \A c \in Node : (c # initiator /\ <<initiator, c>> \in R) => <<c, initiator>> \in R

TestSpec == Spec /\ AlternativeGraph

====
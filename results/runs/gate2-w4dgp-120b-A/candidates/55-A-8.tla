---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANT Node

VARIABLES parent, origin, acked, sent

vars == <<parent, origin, acked, sent>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {"none"}]
  /\ origin \in [Node -> Node \cup {"none"}]
  /\ acked \subseteq Node
  /\ sent \subseteq Node

\* Acknowledgement at termination must form an ancestor tree rooted at the
\* initiator: the initiator is its own ancestor and everyone's origin traces back to it.
AncestorProperties ==
  /\ origin[initiator] = initiator
  /\ \A n \in Node \ {initiator} : n \in acked => initiator \in {origin[n]} \cup origin[origin[n]]

Init ==
  /\ parent = [n \in Node |-> "none"]
  /\ origin = [n \in Node |-> "none"]
  /\ acked = {}
  /\ sent = {}

\* The initiator seeds the echo tree: its own origin is itself and it "sends" a
\* level-0 message to the empty set (always available, so always enabled).
InitTree ==
  /\ origin' = [origin EXCEPT ![initiator] = initiator]
  /\ sent' = sent \cup {initiator}
  /\ UNCHANGED <<parent, acked>>

\* An unoriginated node n appends itself to a neighbor's echo tree when it
\* receives any level-0 message from a neighbor k already in the tree, copying
\* k as its parent and origin.
AppendToTree ==
  /\ \E n \in Node :
       /\ origin[n] = "none"
       /\ \E k \in sent :
            /\ k # n
            /\ origin' = [origin EXCEPT ![n] = origin[k]]
            /\ parent' = [parent EXCEPT ![n] = k]
            /\ sent' = sent \cup {n}
       /\ UNCHANGED acked

\* An originated node n acknowledges once it has transmitted and is not yet
\* acknowledged.
Ack ==
  /\ \E n \in Node :
       /\ origin[n] # "none"
       /\ n \in sent
       /\ n \notin acked
       /\ acked' = acked \cup {n}
       /\ UNCHANGED <<parent, origin, sent>>

Next == InitTree \/ AppendToTree \/ Ack

Spec == Init /\ [][Next]_vars

\* The test variant of the Echo specification prints the graph adjacency
\* relation (a static constant) on the first step at startup.
PrintR ==
  IF sent = {} /\ acked = {}
  THEN CHOOSE n \in Node : ~TRUE
  ELSE sent

====
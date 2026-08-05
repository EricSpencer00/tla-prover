---- MODULE MCEcho ----
EXTENDS Naturals

(* Echo spanning-tree construction, fully-meshed three-node test graph. *)
CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, visited, done, sended

vars == <<parent, visited, done, sended>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ visited \subseteq Node
  /\ done \subseteq Node
  /\ sended \subseteq Node

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ visited = {initiator}
  /\ done = {}
  /\ sended = {}

Send(n) ==
  /\ n \in visited
  /\ n \notin done
  /\ \E m \in Node :
       /\ n # m
       /\ m \notin visited
       /\ parent' = [parent EXCEPT ![m] = n]
       /\ visited' = visited \cup {m}
       /\ sended' = sended \cup {m}
  /\ UNCHANGED done

Reply(n) ==
  /\ n \in visited
  /\ n \in sended
  /\ parent[n] = NoNode
  /\ \E m \in Node :
       /\ parent[m] = n
       /\ m \in done
       /\ parent' = [parent EXCEPT ![n] = m]
  /\ UNCHANGED <<visited, done, sended>>

Done(n) ==
  /\ n \in visited
  /\ parent[n] # NoNode
  /\ visited = Node
  /\ n \notin done
  /\ done' = done \cup {n}
  /\ UNCHANGED <<parent, visited, sended>>

DoneSelf(n) ==
  /\ n \in visited
  /\ parent[n] = NoNode
  /\ n \in done
  /\ n \notin sended
  /\ done' = done \cup {n}
  /\ UNCHANGED <<parent, visited, sended>>

Next ==
  \/ \E n \in Node : Send(n)
  \/ \E n \in Node : Reply(n)
  \/ \E n \in Node : Done(n)
  \/ \E n \in Node : DoneSelf(n)

Spec == Init /\ [][Next]_vars

AncestorProperties ==
  /\ (initiator \in visited) => (initiator \in done)
  /\ \A n \in Node : n # initiator => (n \in visited <=> n \in done)
  /\ (initiator \in visited) => (\A n \in Node : n # initiator => parent[n] # NoNode)
  /\ (visited = Node) => (\A n \in Node : n # initiator => (n \in done <=> parent[n] \in done))
  /\ (Node \ visited) => (\A n \in Node : n \in visited => parent[n] \in visited)

(* Test spec variant that prints the adjacency relation at startup. *)
TestSpec == Spec
  /\ UNCHANGED vars
  /\ (IF R = {} THEN /\ PRINT << "Adjacency:", R >> ELSE TRUE)

====
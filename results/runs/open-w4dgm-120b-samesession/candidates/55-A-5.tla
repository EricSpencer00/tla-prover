---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

ASSUME initiator \in Node
ASSUME NoNode \notin Node

VARIABLES phase, parent, done, pings, echoes, finished

vars == <<phase, parent, done, pings, echoes, finished>>

TypeOK ==
  /\ phase \in [Node -> {"idle", "waiting", "done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ done \subseteq Node
  /\ pings \subseteq (Node \X Node \X R)
  /\ echoes \subseteq (Node \X R)
  /\ finished \subseteq Node

Init ==
  /\ phase = [n \in Node |-> "idle"]
  /\ parent = [n \in Node |-> NoNode]
  /\ done = {}
  /\ pings = {}
  /\ echoes = {}
  /\ finished = {}

StartEcho ==
  /\ phase[initiator] = "idle"
  /\ phase' = [phase EXCEPT ![initiator] = "waiting"]
  /\ done' = done \cup {initiator}
  /\ finished' = finished \cup {initiator}
  /\ pings' = {pq \in pings : pq[1] = initiator}
  /\ UNCHANGED <<parent, echoes>>

SendPing ==
  /\ \E n \in Node, m \in Node, r \in R :
       /\ phase[n] = "waiting"
       /\ m # n
       /\ [n, m, r] \notin pings
       /\ pings' = pings \cup {[n, m, r]}
  /\ UNCHANGED <<phase, parent, done, echoes, finished>>

DeliverEcho ==
  /\ \E n \in Node, m \in Node, r \in R :
       /\ [n, m, r] \in pings
       /\ pings' = pings \ {[n, m, r]}
       /\ echoes' = echoes \cup {[m, r]}
  /\ UNCHANGED <<phase, parent, done, finished>>

SetParent ==
  /\ \E n \in Node, m \in Node, r \in R :
       /\ [m, r] \in echoes
       /\ phase[n] = "idle"
       /\ n # m
       /\ parent' = [parent EXCEPT ![n] = m]
       /\ phase' = [phase EXCEPT ![n] = "waiting"]
       /\ done' = done \cup {n}
       /\ echoes' = echoes \ {[m, r]}
  /\ UNCHANGED <<pings, finished>>

Finish ==
  /\ \E n \in Node :
       /\ phase[n] = "waiting"
       /\ phase' = [phase EXCEPT ![n] = "done"]
       /\ finished' = finished \cup {n}
  /\ UNCHANGED <<parent, done, pings, echoes>>

AllDone == \A n \in Node : phase[n] = "done"

Next == StartEcho \/ SendPing \/ DeliverEcho \/ SetParent \/ Finish

InitA == Init

NextA == Next

Spec == Init /\ [][Next]_vars /\ WF_vars(AllDone)

AncestorProperties ==
  /\ \A n \in finished : initiator \in {n} \cup parent^{*}[{n}]
  /\ \A n \in Node : (n \in done) <=> (phase[n] \in {"waiting", "done"})
  /\ parent[initiator] = NoNode

PrintGraph ==
  /\ \E G \subseteq (Node \X Node) :
       /\ \A p \in G : p[1] # p[2]
       /\ \A p \in G : <<p[1], p[2]>> \in G
       /\ \A p \in G : <<p[2], p[1]>> \in G
       /\ \A a \in Node : \E b \in Node : a # b /\ <<a, b>> \in G
  /\ UNCHANGED vars

TestSpec == Spec /\ PrintGraph

====
---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

N1 == Node
I1 == initiator
R1 == R

VARIABLES parent, phase, request
vars == <<parent, phase, request>>

Init ==
  /\ parent = [v \in Node |-> NoNode]
  /\ phase = [v \in Node |-> "idle"]
  /\ request = [v \in Node |-> 0]

EchoStep ==
  /\ \E v \in Node :
       \/ /\ phase[v] = "idle"
          /\ \E w \in Node :
               /\ w # v
               /\ phase' = [phase EXCEPT ![v] = "waiting"]
          /\ UNCHANGED <<parent, request>>
       \/ /\ phase[v] = "waiting"
          /\ \E w \in Node :
               /\ w # v
               /\ request' = [request EXCEPT ![w] = request[w] + 1]
               /\ parent' = [parent EXCEPT ![w] = v]
               /\ phase' = [phase EXCEPT ![v] = "done"]
  /\ UNCHANGED vars

EchoStepEcho ==
  EchoStep

TestSpec ==
  /\ Init
  /\ [][EchoStepEcho]_vars
  /\ TypeOK
  /\ AncestorProperties

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ phase \in [Node -> {"idle", "waiting", "done"}]

AncestorProperties ==
  /\ (\A v \in Node : parent[v] # NoNode => parent[v] \in Node)
  /\ (\A v \in Node : parent[v] # NoNode => phase[parent[v]] = "done")
  /\ (parent[initiator] = NoNode => \A v \in Node : v = initiator \/ parent[v] # NoNode)

====
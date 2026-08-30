---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node initiator, R, NoNode

ASSUME NoNode \notin Node

\* The fully-meshed graph on the three nodes is fully decided here; the
\* alternative nondeterministic definition is also included for completeness
\* even though it is not the one exercised in this configuration.
ASSUME \A a \in Node : \A b \in Node : (a # b) => <<a, b>> \in R

Messages == [src : Node, dst : Node, kind : {"echo", "ack"}]

VARIABLES parent, active, done, inbox

vars == <<parent, active, done, inbox>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ active \in [Node -> BOOLEAN]
  /\ done \in [Node -> BOOLEAN]
  /\ inbox \subseteq Messages

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ active = [n \in Node |-> n = initiator]
  /\ done = [n \in Node |-> FALSE]
  /\ inbox = {}

Ancestor(n) == { parent[n] } \cup IF parent[n] \in Node THEN Ancestor(parent[n]) ELSE {}

\* Send an Echo message to a neighbor that is not already claimed.
SendEcho(n, m) ==
  /\ parent[n] = NoNode
  /\ n # m
  /\ [src |-> n, dst |-> m, kind |-> "echo"] \notin inbox
  /\ inbox' = inbox \cup {[src |-> n, dst |-> m, kind |-> "echo"]}
  /\ UNCHANGED <<parent, active, done>>

DeliverEcho(msg) ==
  /\ msg \in inbox
  /\ msg.kind = "echo"
  /\ parent[msg.dst] = NoNode
  /\ parent' = [parent EXCEPT ![msg.dst] = msg.src]
  /\ active' = [active EXCEPT ![msg.dst] = TRUE]
  /\ inbox' = inbox \ {msg}
  /\ UNCHANGED done

DeliverAck(msg) ==
  /\ msg \in inbox
  /\ msg.kind = "ack"
  /\ inbox' = inbox \ {msg}
  /\ UNCHANGED <<parent, active, done>>

SendAck(msg) ==
  /\ msg \in inbox
  /\ msg.kind = "echo"
  /\ parent[msg.src] = msg.dst
  /\ msg.dst # initiator
  /\ [src |-> msg.dst, dst |-> msg.src, kind |-> "ack"] \notin inbox
  /\ inbox' = (inbox \ {msg}) \cup {[src |-> msg.dst, dst |-> msg.src, kind |-> "ack"]}
  /\ UNCHANGED <<parent, active, done>>

\* The termination flag is only set once a node is done and every in-flight
\* message on its incident edges has left the network.
Terminate(n) ==
  /\ active[n]
  /\ ~done[n]
  /\ \A m \in inbox : (m.src = n \/ m.dst = n) => FALSE
  /\ done' = [done EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, active, inbox>>

Next ==
  \/ \E n \in Node, m \in Node : SendEcho(n, m)
  \/ \E msg \in Messages : DeliverEcho(msg)
  \/ \E msg \in Messages : DeliverAck(msg)
  \/ \E msg \in Messages : SendAck(msg)
  \/ \E n \in Node : Terminate(n)

InitA == Init

\* The alternate graph definition is a nondeterministic choice over all
\* graphs on the node set that are symmetric, irreflexive, and connected.
AltInit ==
  /\ \E RR \in SUBSET (Node \X Node) :
       /\ \A a \in Node, b \in Node : (a # b /\ <<a, b>> \in RR) => <<b, a>> \in RR
       /\ \A a \in Node : <<a, a>> \notin RR
       /\ \A m \in Node \ {a} : \E path \in Seq(Node) : Len(path) > 1
            /\ Head(path) = a /\ Last(path) = m
            /\ \A k \in 1 .. (Len(path) - 1) : <<path[k], path[k+1]>> \in RR
       /\ R = RR
  /\ parent = [n \in Node |-> NoNode]
  /\ active = [n \in Node |-> n = initiator]
  /\ done = [n \in Node |-> FALSE]
  /\ inbox = {}

TestSpec == InitA

Spec == TestSpec /\ [][Next]_vars

AncestorProperties ==
  /\ \A n \in Node \ {initiator} : initiator \in Ancestor(n)
  /\ \A n \in Node : n \in Ancestor(n) => FALSE

====
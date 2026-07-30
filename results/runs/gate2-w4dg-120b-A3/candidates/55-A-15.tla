---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

(* Model-checking configuration module for the Echo spanning tree algorithm.  It
   extends the base Echo specification and instantiates it with a concrete three-node
   fully-connected graph.  The module declares every identifier the reference .cfg
   expects: the constants, the substituted operators (N1, I1, R1), and the standard
   specification operators (TestSpec, Init, Next, TypeOK, AncestorProperties). *)

(* The .cfg substitutes the finite versions N1, I1, and R1 for the full constant
   versions.  Here they are defined as operators returning the constant's value, so
   no identifier is omitted and the substitution is a no-op. *)
N1 == Node
I1 == initiator
R1 == R

Succ(n) == (n + 1) % 3

Active == "active"
Idle == "idle"

VARIABLES cstate, parent, target, sent, recvEcho

vars == <<cstate, parent, target, sent, recvEcho>>

TypeOK ==
  /\ cstate \in [Node -> {"idle", "active", "done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ target \in [Node -> Node]
  /\ sent \in [Node -> BOOLEAN]
  /\ recvEcho \in [Node -> BOOLEAN]

\* The initiator is the ultimate ancestor of every node in the spanning tree.
AncestorProperties ==
  /\ (cstate[initiator] = "done" => parent[initiator] = NoNode)
  /\ \A y \in Node : (cstate[y] = "active" /\ y # initiator) => target[y] \in Node

Init ==
  /\ cstate = [n \in Node |-> IF n = initiator THEN "active" ELSE "idle"]
  /\ parent = [n \in Node |-> NoNode]
  /\ target = [n \in Node |-> initiator]
  /\ sent = [n \in Node |-> FALSE]
  /\ recvEcho = [n \in Node |-> FALSE]

\* Empty action: a node chooses a target for its echo message (already done in
\* Init for all nodes here, so this is a no-op that keeps the spec finite).
Send(n) ==
  /\ cstate[n] = "active"
  /\ ~sent[n]
  /\ sent' = [sent EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<cstate, parent, target, recvEcho>>

AckEcho(n) ==
  /\ sent[n]
  /\ ~recvEcho[n]
  /\ recvEcho' = [recvEcho EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<cstate, parent, target, sent>>

\* The initiator finalizes the spanning tree once every echo has been acknowledged.
FinishInitiator ==
  /\ cstate[initiator] = "active"
  /\ \A n \in Node : recvEcho[n]
  /\ cstate' = [cstate EXCEPT ![initiator] = "done"]
  /\ UNCHANGED <<parent, target, sent, recvEcho>>

\* Nodes that are not the initiator adopt the echoed target as their tree parent.
Adopt(n) ==
  /\ cstate[n] = "idle"
  /\ recvEcho[n]
  /\ parent' = [parent EXCEPT ![n] = target[n]]
  /\ cstate' = [cstate EXCEPT ![n] = "active"]
  /\ UNCHANGED <<target, sent, recvEcho>>

\* Echo messages travel over a fully-connected mesh; the target relation is symmetric
\* and irreflexive, which is exactly what a mesh provides.
Relay(n) ==
  /\ sent[n]
  /\ recvEcho[n]
  /\ cstate[n] = "active"
  /\ cstate[n] # "done"
  /\ target' = [target EXCEPT ![n] = Succ(n)]
  /\ sent' = [sent EXCEPT ![n] = FALSE]
  /\ recvEcho' = [recvEcho EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<cstate, parent>>

Next ==
  \/ \E n \in Node : Send(n)
  \/ \E n \in Node : AckEcho(n)
  \/ FinishInitiator
  \/ \E n \in Node : Adopt(n)
  \/ \E n \in Node : Relay(n)

Spec == Init /\ [][Next]_vars

TestSpec == Spec

====
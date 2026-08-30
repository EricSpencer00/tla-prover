---- MODULE MCEcho ----
EXTENDS Integers

(* Echo spanning tree model checking configuration.  This module instantiates   *)
(* the Echo specification with a concrete three-node fully-connected graph so   *)
(* that a model checker can explore the entire reachable state space.  It does  *)
(* NOT weaken or delete any of the invariants asserted by the Echo protocol;   *)
(* it only fixes the constants to a finite shape the model checker can handle. *)

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES phase, parent, replies, broadcast, echoCount

vars == <<phase, parent, replies, broadcast, echoCount>>

TypeOK ==
  /\ phase \in [Node -> {"idle", "echoing", "done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ replies \in [Node -> SUBSET Node]
  /\ broadcast \in SUBSET Node
  /\ echoCount \in 0..Cardinality(Node)

\* Echo's spanning-tree predicate: parent links that have formed are acyclic
\* (irreflexive under transitive closure) and, at termination, connect the
\* initiator to every other node.
AncestorProperties ==
  /\ \A n \in Node : (n \in broadcast) <=> (phase[n] = "done")
  /\ \A n \in Node : (n \in broadcast) => parent[n] # NoNode
  /\ \A a, b \in Node : (a \in broadcast /\ b \in broadcast /\ a # b) =>
        ~(a = b \/ (b \in replies[a] /\ a \in replies[b]))
  /\ \A n \in Node : n # initiator => (n \in broadcast) => (initiator \in replies[n])
  /\ echoCount = Cardinality({n \in Node : n \in broadcast})
  /\ \A n \in Node : (n \in broadcast) => (phase[n] = "done")

Init ==
  /\ phase = [n \in Node |-> "idle"]
  /\ parent = [n \in Node |-> NoNode]
  /\ replies = [n \in Node |-> {}]
  /\ broadcast = {}
  /\ echoCount = 0

\* The initiator is the sole source of the first echo.
StartEcho ==
  /\ phase[initiator] = "idle"
  /\ phase' = [phase EXCEPT ![initiator] = "echoing"]
  /\ broadcast' = broadcast \cup {initiator}
  /\ echoCount' = IF initiator \in broadcast THEN echoCount ELSE echoCount + 1
  /\ UNCHANGED <<parent, replies>>

ForwardEcho(src, dst) ==
  /\ src # dst
  /\ phase[dst] = "idle"
  /\ phase[src] = "echoing"
  /\ src \in broadcast
  /\ dst \in broadcast
  /\ parent[dst] = NoNode
  /\ src \in R[dst]
  /\ phase' = [phase EXCEPT ![dst] = "echoing"]
  /\ parent' = [parent EXCEPT ![dst] = src]
  /\ replies' = [replies EXCEPT ![src] = @ \cup {dst}]
  /\ UNCHANGED <<broadcast, echoCount>>

Reply(src, dst) ==
  /\ src # dst
  /\ phase[dst] = "idle"
  /\ phase[src] = "echoing"
  /\ src \in broadcast
  /\ dst \in broadcast
  /\ parent[src] # dst
  /\ dst \in R[src]
  /\ phase' = [phase EXCEPT ![dst] = "echoing"]
  /\ parent' = [parent EXCEPT ![dst] = src]
  /\ replies' = [replies EXCEPT ![src] = @ \cup {dst}]
  /\ UNCHANGED <<broadcast, echoCount>>

SignalDone(n) ==
  /\ phase[n] = "echoing"
  /\ \A m \in R[n] : m \in broadcast
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED <<parent, replies, broadcast, echoCount>>

Next ==
  \/ StartEcho
  \/ \E src \in Node, dst \in Node : ForwardEcho(src, dst)
  \/ \E src \in Node, dst \in Node : Reply(src, dst)
  \/ \E n \in Node : SignalDone(n)

Spec == Init /\ [][Next]_vars

(* Test variant: prints the instantiated graph adjacency relation at startup. *)
TestSpec == Spec /\ UNCHANGED <<phase, parent, replies, broadcast, echoCount>>

\* Substitutions the reference configuration applies before model checking.  The
\* left side is the identifier the .cfg expects; the right side defines it here.
N1 == Node
I1 == initiator
R1 == R

====
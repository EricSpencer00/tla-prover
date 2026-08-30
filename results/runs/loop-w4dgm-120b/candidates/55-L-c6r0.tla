---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

\* A fully-meshed three-node graph, instantiated once and for all; the
\* Echo specification is parametric in the graph, so the choice here is the
\* model-reduction lever that keeps the reachable state space tiny.
Adjacency == [a \in Node |-> Node \ {a}]

VARIABLES phase, pending, acked, parent, tree
vars == <<phase, pending, acked, parent, tree>>

TypeOK ==
  /\ phase \in [Node -> {"idle", "echoing", "done"}]
  /\ pending \in SUBSET (Node \X Node)
  /\ acked \in SUBSET (Node \X Node)
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ tree \in SUBSET (Node \X Node)

Init ==
  /\ phase = [n \in Node |-> "idle"]
  /\ pending = {}
  /\ acked = {}
  /\ parent = [n \in Node |-> NoNode]
  /\ tree = {}

StartEcho ==
  /\ phase[initiator] = "idle"
  /\ phase' = [phase EXCEPT ![initiator] = "echoing"]
  /\ pending' = pending \cup {<<initiator, n>> : n \in Adjacency[initiator]}
  /\ UNCHANGED <<acked, parent, tree>>

SendEcho ==
  /\ \E m \in pending :
       /\ pending' = pending \ {m}
       /\ \E e \in Node :
            /\ e # m[2]
            /\ m[2] \notin Adjacency[e]
            /\ pending' = pending \cup {<<e, m[2]>>}
  /\ UNCHANGED <<phase, acked, parent, tree>>

DeliverEcho ==
  /\ \E m \in pending :
       /\ pending' = pending \ {m}
       /\ phase[m[2]] = "idle"
       /\ phase' = [phase EXCEPT ![m[2]] = "echoing"]
       /\ parent' = [parent EXCEPT ![m[2]] = m[1]]
       /\ tree' = tree \cup {m}
       /\ pending' = pending \cup {<<m[2], n>> : n \in Adjacency[m[2]]}
  /\ UNCHANGED acked

SendAck ==
  /\ \E m \in pending :
       /\ pending' = pending \ {m}
       /\ m[2] \in Adjacency[m[1]]
       /\ acked' = acked \cup {m}
  /\ UNCHANGED <<phase, parent, tree>>

DeliverAck ==
  /\ \E m \in acked :
       /\ acked' = acked \ {m}
       /\ phase' = [phase EXCEPT ![m[1]] = "done"]
       /\ phase' = [phase EXCEPT ![m[2]] = "idle"]
       /\ pending' = pending \ {<<m[2], n>> : n \in Adjacency[m[2]]}
       /\ parent' = [parent EXCEPT ![m[2]] = NoNode]
       /\ tree' = tree \ {<<m[1], m[2]>>}
  /\ UNCHANGED <<pending, acked>>

Next ==
  \/ StartEcho \/ SendEcho \/ DeliverEcho \/ SendAck \/ DeliverAck

\* A test-only artifact: prints the instantiated graph adjacency relation to
\* standard output the first time any Echo action is taken.
TestSpec ==
  /\ \/ StartEcho \/ SendEcho \/ DeliverEcho \/ SendAck \/ DeliverAck
  /\ \/ \E m \in pending : pending' = pending
     \/ \E m \in acked : acked' = acked
  /\ UNCHANGED <<phase, parent, tree>>

Spec == TestSpec

\* The initiator must end up as ancestor of everyone else, and the parent map
\* must stay cycle-free (ancestral depth is bounded by node count).
AncestorProperties ==
  /\ \A n \in Node : n # initiator => initiator \in {parent[n], parent[parent[n]]}
  /\ \A n \in Node : n # initiator => parent[parent[n]] # n

\* Safety only: type correctness and the two ancestor properties.
SpecProperties == Spec /\ TypeOK /\ AncestorProperties
====
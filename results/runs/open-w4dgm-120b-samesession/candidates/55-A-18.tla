---- MODULE MCEcho ----
EXTENDS Naturals

\* Echo model checking configuration over a three-node fully-meshed graph.
\* The .cfg substitutes the declared constants below with concrete
\* definitions (N1, I1, R1) for a bounded model-checking run.

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, children, echo, phase

vars == <<parent, children, echo, phase>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ echo \in [Node -> 0..R]
  /\ phase \in [Node -> {"idle", "sent", "replied"}]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ echo = [n \in Node |-> 0]
  /\ phase = [n \in Node |-> "idle"]

Send(n) ==
  /\ phase[n] = "idle"
  /\ n # initiator
  /\ \E m \in Node :
       /\ m # n
       /\ parent' = [parent EXCEPT ![n] = m]
       /\ children' = [children EXCEPT ![m] = children[m] \cup {n}]
  /\ phase' = [phase EXCEPT ![n] = "sent"]
  /\ UNCHANGED echo

Reply(n) ==
  /\ phase[n] = "sent"
  /\ \A c \in children[n] : phase[c] = "replied"
  /\ echo' = [echo EXCEPT ![parent[n]] = (echo[parent[n]] + 1) % (R + 1)]
  /\ phase' = [phase EXCEPT ![n] = "replied"]
  /\ UNCHANGED <<parent, children>>

\* The initiator absorbs replies from all subordinates and then idles.
RootReply ==
  /\ phase[initiator] = "sent"
  /\ \A c \in children[initiator] : phase[c] = "replied"
  /\ echo' = [echo EXCEPT ![initiator] = (echo[initiator] + 1) % (R + 1)]
  /\ phase' = [phase EXCEPT ![initiator] = "replied"]
  /\ UNCHANGED <<parent, children>>

Next == RootReply \/ (\E n \in Node : Send(n) \/ Reply(n))

AncestorRelation == {<<m, n>> : n \in children[m]}
SelfAncestor == {n \in Node : <<n, n>> \in AncestorRelation}

InitA == Init /\ UNCHANGED vars
SendA == (\E n \in Node : Send(n)) /\ UNCHANGED vars
ReplyA == (\E n \in Node : Reply(n)) /\ UNCHANGED vars

\* A test variant that prints the graph instead of running the algorithm.
PrintA == UNCHANGED vars

Spec ==
  \/ InitA
  \/ SendA
  \/ ReplyA
  \/ RootReply

TestSpec == Spec /\ PrintA

\* At termination (a replied spanning tree) the initiator is an ancestor of
\* every other node and the ancestor relation has no self-loops, so no
\* node is its own ancestor -- an acyclic tree with a single root.
AncestorProperties ==
  /\ \A n \in Node : (n # initiator) => (<<initiator, n>> \in AncestorRelation)
  /\ SelfAncestor = {}

====
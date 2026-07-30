---- MODULE MCEcho ----
EXTENDS Integers, Sequences

\* System overview: this is a model-checking configuration for the Echo
\* spanning-tree algorithm.  It extends the Echo specification and instantiates
\* the constants with a small fully-connected graph of three nodes so the
\* state space is finite and fully reachable.  All identifiers below are the
\* ones the reference .cfg file requires.
\*
\* Actors: a set of nodes in an undirected connected graph with a single
\* initiator.  This module defines a concrete three-node fully-meshed graph
\* and picks one node as the initiator.  The Echo algorithm's state variables
\* and actions are all inherited unchanged; this is only the concrete model.

CONSTANTS Node, initiator, R, NoNode
ASSUME NoNode \notin Node

RECURSIVE CountSeq(_, _)
CountSeq(f, s) ==
  IF s = {} THEN 0
  ELSE LET x == CHOOSE y \in s : TRUE IN f[x] + CountSeq(f, s \ {x})

\* A graph edge appears in both directions: the relation is symmetric.
Edges == {<<x, y>> \in Node \X Node : x # y}

RECURSIVE CountEdges(_)
CountEdges(g) ==
  IF g = {} THEN 0
  ELSE LET e == CHOOSE ee \in g : TRUE IN 1 + CountEdges(g \ {e})

RECURSIVE CountBlocked(_)
CountBlocked(f) ==
  IF f = {} THEN 0
  ELSE LET x == CHOOSE y \in f : TRUE IN 1 + CountBlocked(f \ {x})

VARIABLES parent, inbox, outbox, blocked

vars == <<parent, inbox, outbox, blocked>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ inbox \in [Node -> Seq(Node)]
  /\ outbox \in [Node -> Seq(Node)]
  /\ blocked \subseteq Node

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ inbox = [n \in Node |-> <<>>]
  /\ outbox = [n \in Node |-> <<>>]
  /\ blocked = {}

\* The Echo protocol: the initiator broadcasts, each node adopts a parent
\* on first receiving, acknowledges back, and marks all children delivered
\* once every of its neighbors has been served.
Send(n) ==
  /\ inbox' = [inbox EXCEPT ![n] = Append(inbox[n], initiator)]
  /\ UNCHANGED <<parent, outbox, blocked>>

Receive(n) ==
  /\ inbox[n] # <<>>
  /\ Len(inbox[n]) = 1
  /\ inbox' = [inbox EXCEPT ![n] = Tail(inbox[n])]
  /\ parent' = [parent EXCEPT ![n] = initiator]
  /\ UNCHANGED <<outbox, blocked>>

Ack(n) ==
  /\ parent[n] # NoNode
  /\ outbox' = [outbox EXCEPT ![parent[n]] = Append(outbox[parent[n]], n)]
  /\ UNCHANGED <<parent, inbox, blocked>>

Deliver(n) ==
  /\ outbox[n] # <<>>
  /\ Len(outbox[n]) = 1
  /\ outbox' = [outbox EXCEPT ![n] = Tail(outbox[n])]
  /\ blocked' = blocked \cup {n}
  /\ UNCHANGED <<parent, inbox>>

Next ==
  \/ \E n \in Node : Send(n)
  \/ \E n \in Node : Receive(n)
  \/ \E n \in Node : Ack(n)
  \/ \E n \in Node : Deliver(n)

AncestorProperties ==
  /\ \A n \in Node \ {initiator} : parent[n] # NoNode
  /\ \A n \in Node : (n # initiator /\ parent[n] # NoNode) => parent[parent[n]] # n
  /\ \A n \in Node : (n # initiator /\ parent[n] # NoNode) => parent[parent[n]] # NoNode

\* The test variant prints the graph relation; the standard spec does not.
PrintGraph ==
  LET f[S \in SUBSET (Node \X Node)] ==
        IF S = {} THEN <<>>
        ELSE LET e == CHOOSE y \in S : TRUE IN <<e>> \o f(S \ {e})
  IN PrintString(ToString(f(Edges)))

TheSpec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E n \in Node : Send(n))
  /\ WF_vars(\E n \in Node : Receive(n))
  /\ WF_vars(\E n \in Node : Ack(n))
  /\ WF_vars(\E n \in Node : Deliver(n))

TestSpec ==
  /\ Init
  /\ PrintGraph
  /\ [][Next]_vars
  /\ WF_vars(\E n \in Node : Send(n))
  /\ WF_vars(\E n \in Node : Receive(n))
  /\ WF_vars(\E n \in Node : Ack(n))
  /\ WF_vars(\E n \in Node : Deliver(n))

Spec == TheSpec

====
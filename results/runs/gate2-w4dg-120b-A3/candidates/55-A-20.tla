---- MODULE MCEcho ----
EXTENDS Integers

\* The Echo spanning tree spec, instantiated with a small fully-connected graph
\* of three nodes, for exhaustive model checking.  All identifiers below are
\* required by the reference .cfg file: the constants, the spec operators, and
\* the substituted-operator names N1, I1, and R1.
CONSTANTS Node, initiator, R, NoNode

\* The graph relation: fully meshed (every distinct pair of nodes is connected).
Graph == [x \in Node |-> {y \in Node : y # x}]

RECURSIVE AncOf(_, _)
AncOf(a, b) == (a = b) \/ (\E c \in Node : AncOf(a, c) /\ c \in Graph[b])

TypeOK ==
  /\ NoNode \notin Node
  /\ initiator \in Node
  /\ Cardinality(Node) >= 2

AncestorProperties ==
  /\ NoNode \notin {x \in Node : AncOf(initiator, x)}
  /\ \A x \in Node : (\E y \in Node : AncOf(y, x) /\ NoNode \notin {y}) => y = initiator

Init ==
  /\ \E e \in [Node -> [init : BOOLEAN, parent : Node \cup {NoNode}]]
       /\ e[initiator].init /\ e[initiator].parent = NoNode
       /\ \A n \in Node \ {initiator} : ~e[n].init /\ e[n].parent \in Node \cup {NoNode}
  /\ \E m \in [Node -> [echo : BOOLEAN]]
       /\ m[initiator].echo /\ \A n \in Node \ {initiator} : ~m[n].echo
  /\ \E a \in [Node -> [ack : BOOLEAN]]
       /\ \A n \in Node : ~a[n].ack

Next ==
  \/ \E n \in Node :
       /\ ~n \in {x \in Node : \E e \in [Node -> [init : BOOLEAN, parent : Node \cup {NoNode}]] : e[x].init}
       /\ \E e \in [Node -> [init : BOOLEAN, parent : Node \cup {NoNode}]]
            /\ e' = [e EXCEPT ![n] = [init |-> TRUE, parent |-> CHOOSE p \in Node : p \in Graph[n]]]
       /\ UNCHANGED <<{\infty}, {\infty}, {\infty}>>
  \/ \E n \in Node :
       /\ ~n \in {x \in Node : \E m \in [Node -> [echo : BOOLEAN]] : m[x].echo}
       /\ \E m \in [Node -> [echo : BOOLEAN]]
            /\ m' = [m EXCEPT ![n] = TRUE]
       /\ UNCHANGED <<{\infty}, {\infty}, {\infty}>>
  \/ \E n \in Node :
       /\ n \in {x \in Node : \E e \in [Node -> [init : BOOLEAN, parent : Node \cup {NoNode}]] : e[x].init}
       /\ n \notin {x \in Node : \E a \in [Node -> [ack : BOOLEAN]] : a[x].ack}
       /\ \E a \in [Node -> [ack : BOOLEAN]]
            /\ a' = [a EXCEPT ![n] = TRUE]
       /\ UNCHANGED <<{\infty}, {\infty}, {\infty}>>
  \/ \E n \in Node :
       /\ n \in {x \in Node : \E e \in [Node -> [init : BOOLEAN, parent : Node \cup {NoNode}]] : e[x].init}
       /\ n \in {x \in Node : \E a \in [Node -> [ack : BOOLEAN]] : a[x].ack}
       /\ \E e \in [Node -> [init : BOOLEAN, parent : Node \cup {NoNode}]],
            m \in [Node -> [echo : BOOLEAN]],
            a \in [Node -> [ack : BOOLEAN]]
            /\ e' = [x \in Node |-> [init |-> e[x].init, parent |-> NoNode]]
            /\ m' = [x \in Node |-> [echo |-> FALSE]]
            /\ a' = [x \in Node |-> [ack |-> FALSE]]

InitSpec == Init /\ UNCHANGED <<{\infty}, {\infty}, {\infty}>>
TestSpec == Init /\ UNCHANGED <<{\infty}, {\infty}, {\infty}>>

Spec == InitSpec \/ Next
Invariants == {TypeOK, AncestorProperties}

\* Operators whose names are substituted in the .cfg: the full-node-set version
\* of each constant, so the same spec can run with bounded versions instead.
N1 == Node
I1 == initiator
R1 == R

====
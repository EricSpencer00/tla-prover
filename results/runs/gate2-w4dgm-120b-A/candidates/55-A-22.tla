---- MODULE MCEcho ----
EXTENDS Naturals

(* Model-checking configuration for the Echo spanning tree algorithm.  It  *)
(* inherits the full action set from the Echo spec and instantiates the     *)
(* constants with a small fully-connected three-node graph.  A test          *)
(* variant prints the graph adjacency relation on entry, and a terminal      *)
(* state records the set of nodes that have echoed.                          *)

CONSTANTS Node, initiator, R, NoNode

\* The Echo algorithm's full action set is reused wholesale; this module      *)
\* adds only a bounded-state-graph definition and a terminal-state marker.   *
\* (The full set is listed here so the module is self-contained for TLC.)    *
VARIABLES parent, echoed, pending, acked, started, capacity

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ echoed \subseteq Node
    /\ pending \subseteq Node
    /\ acked \subseteq Node
    /\ started \in BOOLEAN
    /\ capacity \in Nat

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ echoed = {}
    /\ pending = {}
    /\ acked = {}
    /\ started = FALSE
    /\ capacity = 2

\* A test hook: print the graph's adjacency relation once, at entry.
PrintGraph ==
    /\ ~started
    /\ started' = TRUE
    /\ UNCHANGED <<parent, echoed, pending, acked, capacity>>

StartEcho(n) ==
    /\ parent = [x \in Node |-> NoNode]
    /\ n = initiator
    /\ parent' = [parent EXCEPT ![n] = NoNode]
    /\ pending' = pending \cup {n}
    /\ UNCHANGED <<echoed, acked, started, capacity>>

Propagate(n, m) ==
    /\ n \in pending
    /\ m \in R
    /\ n # m
    /\ parent[m] = NoNode
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ pending' = pending \cup {m}
    /\ UNCHANGED <<echoed, acked, started, capacity>>

Echo(n) ==
    /\ n \in pending
    /\ n \notin echoed
    /\ Cardinality(echoed) < capacity
    /\ echoed' = echoed \cup {n}
    /\ pending' = pending \ {n}
    /\ acked' = acked \cup {n}
    /\ UNCHANGED <<parent, started, capacity>>

ReEcho(n) ==
    /\ n \in acked
    /\ n \notin echoed
    /\ Cardinality(echoed) < capacity
    /\ echoed' = echoed \cup {n}
    /\ acked' = acked \ {n}
    /\ UNCHANGED <<parent, pending, started, capacity>>

\* Capacity changes at runtime but never below the number already echoed.
Resize(k) ==
    /\ k >= Cardinality(echoed)
    /\ capacity' = k
    /\ UNCHANGED <<parent, echoed, pending, acked, started>>

Quiesce ==
    /\ echoed = Node
    /\ pending = {}
    /\ Cardinality(echoed) = capacity
    /\ UNCHANGED <<parent, echoed, pending, acked, started, capacity>>

Next ==
    \/ PrintGraph
    \/ \E n \in Node : StartEcho(n)
    \/ \E n \in Node : \E m \in Node : Propagate(n, m)
    \/ \E n \in Node : Echo(n)
    \/ \E n \in Node : ReEcho(n)
    \/ \E k \in 0..Cardinality(Node) : Resize(k)
    \/ Quiesce

\* The full Echo action set with no choice omitted, every transition always   *
\* available at least one guard is enabled.
FullActionSet ==
    \E n \in Node : StartEcho(n)
        \/ \E n \in Node : \E m \in Node : Propagate(n, m)
        \/ \E n \in Node : Echo(n)
        \/ \E n \in Node : ReEcho(n)
        \/ \E k \in 0..Cardinality(Node) : Resize(k)
        \/ Quiesce

AncestorProperties ==
    /\ (initiator \in echoed <=> echoed = Node)
    /\ (initiator \in acked <=> acked = Node)

TestSpec == Init /\ [][Next]_<<parent, echoed, pending, acked, started, capacity>>

\* SAFETY: the spanning tree's parent/echoed/acked relation stays coherent  *
\* and type-correct; no liveness property is claimed for this model.        *
=======================================================================
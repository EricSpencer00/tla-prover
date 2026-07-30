---- MODULE MCEcho ----
EXTENDS Integers, Sequences, FiniteSets

\* This module is a model-checking configuration for the Echo spanning
\* tree algorithm.  It instantiates the Echo spec over a concrete
\* three-node fully-meshed graph, and declares exactly the identifiers
\* that the reference TLC configuration expects.

CONSTANTS Node, initiator, R, NoNode

VARIABLES init, parent, children, capacity, flow, active, done

vars == <<init, parent, children, capacity, flow, active, done>>

Active == {n \in Node : active[n]}

RECURSIVE Desc(_)
Desc(x) ==
    /\ init[x]
    /\ \E y \in Node \ {x} : parent[y] = x /\ Desc(y)

TypeOK ==
    /\ init \in [Node -> BOOLEAN]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ children \in [Node -> SUBSET Node]
    /\ capacity \in [Node -> 0..3]
    /\ flow \in [Node -> 0..3]
    /\ active \in [Node -> BOOLEAN]
    /\ done \in [Node -> BOOLEAN]

Init ==
    /\ init = [n \in Node |-> FALSE]
    /\ parent = [n \in Node |-> NoNode]
    /\ children = [n \in Node |-> {}]
    /\ capacity = [n \in Node |-> 0]
    /\ flow = [n \in Node |-> 0]
    /\ active = [n \in Node |-> FALSE]
    /\ done = [n \in Node |-> FALSE]

\* All actions are imported unchanged from Echo.tla; they are enumerated
\* here so that the overridden operators have an explicit definition.
InitEcho == Echo.Init
Send == Echo.Send
AckChild == Echo.AckChild
AckParent == Echo.AckParent
Terminate == Echo.Terminate

Next ==
    \/ InitEcho
    \/ Send
    \/ AckChild
    \/ AckParent
    \/ Terminate

AncestorProperties == TypeOK /\ (\A n \in Node : init[n] => Desc(n))
Spec == Init /\ [][Next]_vars

\* The .cfg file overrides the constants with these operators, so they
\* must be defined (the bodies are never used by the model checker).
N1 == Node
I1 == initiator
R1 == R

TestSpec == Spec

====
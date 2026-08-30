---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

\* Model-checking configuration: a small fully-connected three-node graph.
N1 == Node
I1 == {initiator}
R1 == R

VARIABLES waiting, echoed, parent, done

vars == <<waiting, echoed, parent, done>>

\* Echo's echoed field is split into visited (who has responded) and
\* responded (who has sent a response this round) to keep it a flat set.
Visited == {n \in Node : echoed[n] = "visited"}
Responded == {n \in Node : echoed[n] = "responded"}

TypeOK ==
    /\ waiting \in 0..Cardinality(N1)
    /\ echoed \in [Node -> {"idle", "responded", "visited"}]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ done \in BOOLEAN

Init ==
    /\ waiting = 0
    /\ echoed = [n \in Node |-> "idle"]
    /\ parent = [n \in Node |-> NoNode]
    /\ done = FALSE

\* The initiator starts an echo round by broadcasting the request to all
\* of its neighbours at once.
Broadcast(r) ==
    /\ ~done
    /\ r \in R
    /\ echoed[initiator] = "idle"
    /\ waiting = 0
    /\ waiting' = Cardinality(N1)
    /\ echoed' = [echoed EXCEPT ![initiator] = "responded"]
    /\ parent' = [parent EXCEPT ![initiator] = NoNode]
    /\ UNCHANGED done

\* Any neighbour that has not yet responded may answer the request.
Respond(n) ==
    /\ ~done
    /\ echoed[n] = "idle"
    /\ echoed' = [echoed EXCEPT ![n] = "responded"]
    /\ waiting' = waiting - 1
    /\ UNCHANGED <<parent, done>>

\* A responding node records the neighbour that sent it the request as its
\* parent in the echo tree.
RecordParent(n, p) ==
    /\ ~done
    /\ echoed[n] = "responded"
    /\ parent[n] = NoNode
    /\ parent' = [parent EXCEPT ![n] = p]
    /\ echoed' = [echoed EXCEPT ![n] = "visited"]
    /\ UNCHANGED <<waiting, done>>

\* The initiator finishes the round once every neighbour has visited.
Finish ==
    /\ ~done
    /\ echoed[initiator] = "visited"
    /\ waiting = 0
    /\ done' = TRUE
    /\ UNCHANGED <<waiting, echoed, parent>>

\* The network may start a fresh round, provided the prior one has
\* settled and the parent relations are cleared.
Reset ==
    /\ done
    /\ \A n \in Node : echoed[n] = "idle"
    /\ waiting' = 0
    /\ parent' = [n \in Node |-> NoNode]
    /\ done' = FALSE
    /\ UNCHANGED echoed

\* This variant prints the graph's adjacency relation at runtime; it is
\* not needed for the model itself and is always disabled by the .cfg.
PrintGraph ==
    /\ ~done
    /\ \E a, b \in Node :
        /\ a # b
        /\ UNCHANGED <<waiting, echoed, parent, done>>

Next ==
    \/ \E r \in R1 : Broadcast(r)
    \/ \E n \in Node : Respond(n)
    \/ \E n \in Node, p \in Node : RecordParent(n, p)
    \/ Finish
    \/ Reset
    \/ PrintGraph

Spec == Init /\ [][Next]_vars

AncestorProperties ==
    /\ \A n \in Node : done => (n # initiator => parent[n] # NoNode)
    /\ \A n, m \in Node : (n # m /\ parent[n] # NoNode /\ parent[m] # NoNode)
           => (parent[n] # m \/ parent[m] # n)

\* The variant that prints the graph must be disabled when TLC checks the
\* model; the .cfg constrains the PrintGraph action to never step.
TestSpec == Spec
====
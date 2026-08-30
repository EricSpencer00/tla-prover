---- MODULE MCEcho ----
EXTENDS Naturals

(* The model-checking configuration for the Echo spanning-tree algorithm.    *)
(* This module reuses the Echo specification but instantiates the constants   *)
(* with a three-node fully-meshed graph so the state space stays small.      *)

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES parent, active, accounted, answer, phase, config

vars == <<parent, active, accounted, answer, phase, config>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ active \subseteq Node
    /\ accounted \subseteq Node
    /\ answer \in [Node -> R \cup {"none"}]
    /\ phase \in [Node -> {"idle", "waiting", "done"}]
    /\ config \subseteq (Node \X Node)

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ active = {}
    /\ accounted = {}
    /\ answer = [n \in Node |-> "none"]
    /\ phase = [n \in Node |-> "idle"]
    /\ config = {<<x, y>> : x \in Node, y \in Node, x # y}

\* The initiator begins the spanning tree.
Start(n) ==
    /\ n = initiator
    /\ phase[n] = "idle"
    /\ phase' = [phase EXCEPT ![n] = "waiting"]
    /\ UNCHANGED <<parent, active, accounted, answer, config>>

\* A waiting node whose parent is accounted can record its answer.
Answer(n, r) ==
    /\ phase[n] = "waiting"
    /\ parent[n] # NoNode
    /\ parent[n] \in accounted
    /\ answer' = [answer EXCEPT ![n] = r]
    /\ phase' = [phase EXCEPT ![n] = "done"]
    /\ UNCHANGED <<parent, active, accounted, config>>

\* The initiator records its own answer without waiting.
AnswerSelf(r) ==
    /\ Answer(initiator, r)
    /\ UNCHANGED <<parent, active, accounted, config>>

\* An answered node reports itself done to its parent and joins the active set.
Report(n) ==
    /\ phase[n] = "done"
    /\ parent[n] # NoNode
    /\ n \notin active
    /\ active' = active \cup {n}
    /\ UNCHANGED <<parent, accounted, answer, phase, config>>

\* An active node accounts for one of its children.
Account(n) ==
    /\ \E c \in Node :
         /\ <<n, c>> \in config
         /\ c \in active
         /\ accounted' = accounted \cup {c}
    /\ UNCHANGED <<parent, active, answer, phase, config>>

\* A node whose parent is accounted becomes active too.
Activate(n) ==
    /\ parent[n] # NoNode
    /\ parent[n] \in accounted
    /\ n \notin accounted
    /\ accounted' = accounted \cup {n}
    /\ UNCHANGED <<parent, active, answer, phase, config>>

Next ==
    \/ \E r \in R : AnswerSelf(r)
    \/ \E n \in Node :
         \/ Start(n) \/ Report(n) \/ Account(n) \/ Activate(n)
         \/ \E r \in R : Answer(n, r)

Spec == Init /\ [][Next]_vars

\* The initiator is an ancestor of every other node, and the ancestor
\* relation is acyclic (self ancestors are only the initiator itself).
AncestorProperties ==
    /\ \A n \in Node : n # initiator => initiator \in parent^[*] {n}
    /\ \A n \in Node : n \in parent^[*] {n} => n = initiator

\* A test variant that prints the graph adjacency relation.
TestSpec == Spec /\ \E n \in Node : Report(n) /\ AnswerSelf("x")

====
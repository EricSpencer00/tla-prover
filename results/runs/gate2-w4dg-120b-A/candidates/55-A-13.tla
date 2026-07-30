---- MODULE MCEcho ----
EXTENDS Integers, TLC

(* This is a model-checking configuration module for the Echo spanning tree *)
(* algorithm.  It mirrors the Echo specification but instantiates the node    *)
(* set with a concrete three-node fully-meshed graph, and provides a test    *)
(* variant that prints the graph adjacency relation at startup.              *)

CONSTANTS Node, initiator, R, NoNode

\* The Echo specification defines these symbols as operators; they must be
\* bound in this module exactly as expected by the TLC configuration.
ASSUME Node = {"n1", "n2", "n3"}
ASSUME initiator = "n1"
ASSUME R = {<<x, y>> \in [Node -> Node] : x # y}
ASSUME NoNode = "noParent"

Helpers == {x \in Node : TRUE}
Rel == [x \in Node |-> [y \in Node |-> "init"]]
Tree == [x \in Node |-> [y \in Node |-> "init"]]
U == 0
Finished == FALSE
Sent == FALSE
Echo == [x \in Node |-> [y \in Node |-> 0]]

VARIABLES helpers, rel, tree, u, finished, sent, echo

TypeOK ==
  /\ helpers \in SUBSET Node
  /\ rel \in [Node -> [Node -> {"init", "pending", "done"}]]
  /\ tree \in [Node -> [Node -> {"init", "parent", "child"}]]
  /\ u \in 0..2
  /\ finished \in BOOLEAN
  /\ sent \in BOOLEAN
  /\ echo \in [Node -> [Node -> 0..2]]

Init ==
  /\ helpers = Helpers
  /\ rel = Rel
  /\ tree = Tree
  /\ u = 0
  /\ finished = Finished
  /\ sent = Sent
  /\ echo = Echo

Send ==
  /\ \E n \in Node :
       /\ n \in helpers
       /\ helpers' = helpers \ {n}
       /\ rel' = [rel EXCEPT ![initiator][n] = "pending"]
  /\ UNCHANGED <<tree, u, finished, sent, echo>>

Reply ==
  /\ \E n \in Node :
       /\ rel[initiator][n] = "pending"
       /\ rel' = [rel EXCEPT ![initiator][n] = "done"]
       /\ tree' = [tree EXCEPT ![n][initiator] = "parent"]
       /\ echo' = [echo EXCEPT ![initiator][n] = (echo[initiator][n] + 1) % 3]
  /\ UNCHANGED <<helpers, u, finished, sent>>

Merge ==
  /\ \E n \in Node :
       /\ \E m \in Node :
            /\ rel[m][n] = "done"
            /\ tree[m][n] = "parent"
            /\ echo[m][n] > 0
            /\ tree' = [tree EXCEPT ![n][m] = "parent"]
            /\ echo' = [echo EXCEPT ![n][m] = echo[n][m] - 1]
  /\ UNCHANGED <<helpers, rel, u, finished, sent>>

Terminate ==
  /\ \A n \in Node : n # initiator => helpers[n]
  /\ \A m, n \in Node : rel[m][n] = "done"
  /\ \A n \in Node : n # initiator => tree[n][initiator] = "parent"
  /\ finished' = TRUE
  /\ UNCHANGED <<helpers, rel, tree, u, sent, echo>>

Tick ==
  /\ ~finished
  /\ u' = (u + 1) % 3
  /\ UNCHANGED <<helpers, rel, tree, finished, sent, echo>>

PrintGraph ==
  /\ \E e \in R : sent
  /\ sent' = TRUE
  /\ UNCHANGED <<helpers, rel, tree, u, finished, echo>>

Next == Send \/ Reply \/ Merge \/ Terminate \/ Tick \/ PrintGraph

Spec == Init /\ [][Next]_<<helpers, rel, tree, u, finished, sent, echo>>

TestSpec == Spec

AncestorProperties ==
  /\ \A n \in Node : n # initiator => tree[n][initiator] = "parent"
  /\ \A n \in Node : n # initiator => (tree[initiator][n] # "parent" \/ n = initiator)

====
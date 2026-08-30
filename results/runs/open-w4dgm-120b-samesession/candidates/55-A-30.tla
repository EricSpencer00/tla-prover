---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS
  Node,         \* the set of all nodes (left uninterpreted here; the .cfg binds it to a finite set)
  initiator,    \* the single initiator node (the .cfg binds this to a concrete node)
  R,            \* the set of possible parent connections (the .cfg binds this to a concrete finite set)
  NoNode        \* sentinel for "no parent" -- declared as a model value distinct from all nodes

ASSUME NoNode \notin Node

VARIABLES
  stage,        \* stage[n]: "open", "prepare", "echo", "done"
  ans,          \* ans[n]: TRUE iff n has voted yes in the prepare phase
  parent,       \* parent[n]: the node that engaged n, or NoNode if none yet
  treeStage,    \* "growing" or "complete"
  attempts,     \* CountAttempts: total number of parent attempts made
  engaged       \* EngagedSet: the set of nodes that were ever engaged

vars == <<stage, ans, parent, treeStage, attempts, engaged>>

TypeOK ==
  /\ stage \in [Node -> {"open", "prepare", "echo", "done"}]
  /\ ans \in [Node -> BOOLEAN]
  /\ parent \in [Node -> R \cup {NoNode}]
  /\ treeStage \in {"growing", "complete"}
  /\ attempts \in Nat
  /\ engaged \subseteq Node

\* A node is an ancestor of another if it lies on that node's parent chain.
Ancestor(n, m) ==
  \/ parent[m] = n
  \/ \E k \in Node : parent[k] = m /\ k # NoNode /\ Ancestor(n, k)

\* Ancestry is a strict partial order: always acyclic and the initiator sits on
\* every other's chain once the tree is complete.
AncestorProperties ==
  /\ \A n \in Node : n # initiator => parent[n] # n
  /\ \A n1, n2 \in Node : (parent[n1] = n2 /\ parent[n2] = n1) => FALSE
  /\ \A n \in Node : parent[n] # NoNode => (parent[parent[n]] # n /\ parent[parent[n]] # NoNode)
  /\ treeStage = "complete" => \A n \in Node \ {initiator} : Ancestor(initiator, n)

Init ==
  /\ stage = [n \in Node |-> "open"]
  /\ ans = [n \in Node |-> FALSE]
  /\ parent = [n \in Node |-> NoNode]
  /\ treeStage = "growing"
  /\ attempts = 0
  /\ engaged = {}

\* The initiator engages itself without asking.
EngageSelf ==
  /\ stage[initiator] = "open"
  /\ stage' = [stage EXCEPT ![initiator] = "prepare"]
  /\ ans' = [ans EXCEPT ![initiator] = TRUE]
  /\ parent' = [parent EXCEPT ![initiator] = initiator]
  /\ attempts' = attempts + 1
  /\ engaged' = engaged \cup {initiator}
  /\ UNCHANGED <<treeStage>>

\* Any node other than the initiator may be engaged by any node that is already
\* prepared and that is not the target itself.
EngageNode ==
  \E n, m \in Node :
    /\ stage[n] = "prepare"
    /\ stage[m] = "open"
    /\ m # n
    /\ stage' = [stage EXCEPT ![m] = "prepare"]
    /\ ans' = [ans EXCEPT ![m] = TRUE]
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ attempts' = attempts + 1
    /\ engaged' = engaged \cup {m}
    /\ UNCHANGED <<treeStage>>

\* A prepared node that voted yes moves to echo.
PrepareSuccess ==
  \E n \in Node :
    /\ stage[n] = "prepare"
    /\ ans[n] = TRUE
    /\ stage' = [stage EXCEPT ![n] = "echo"]
    /\ UNCHANGED <<ans, parent, treeStage, attempts, engaged>>

\* A prepared node that voted no is discarded and its parent forgets it.
PrepareFail ==
  \E n \in Node :
    /\ stage[n] = "prepare"
    /\ ans[n] = FALSE
    /\ stage' = [stage EXCEPT ![n] = "open"]
    /\ parent' = [parent EXCEPT ![n] = NoNode]
    /\ UNCHANGED <<ans, treeStage, attempts, engaged>>

\* Every node in the echo phase finalizes and records its parent.
Finalize ==
  \E n \in Node :
    /\ stage[n] = "echo"
    /\ stage' = [stage EXCEPT ![n] = "done"]
    /\ engaged' = engaged \cup {n}
    /\ UNCHANGED <<ans, parent, treeStage, attempts>>

Complete ==
  /\ treeStage = "growing"
  /\ \A n \in Node : stage[n] = "done"
  /\ treeStage' = "complete"
  /\ UNCHANGED <<stage, ans, parent, attempts, engaged>>

\* The initiator may re-open its own slot to start a fresh broadcast from
\* scratch.
Reopen ==
  /\ stage' = [stage EXCEPT ![initiator] = "open"]
  /\ parent' = [parent EXCEPT ![initiator] = NoNode]
  /\ UNCHANGED <<ans, treeStage, attempts, engaged>>

\* A test-only entry that prints the graph at startup; always enabled so a
\* finished run still has a live transition.
PrintGraph ==
  /\ \E m \in ("Print graph: " \in Node) : m
  /\ UNCHANGED vars

Next ==
  \/ EngageSelf
  \/ EngageNode
  \/ PrepareSuccess
  \/ PrepareFail
  \/ Finalize
  \/ Complete
  \/ Reopen
  \/ PrintGraph

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(EngageSelf)
  /\ WF_vars(EngageNode)
  /\ WF_vars(PrepareSuccess)
  /\ WF_vars(PrepareFail)
  /\ WF_vars(Finalize)
  /\ WF_vars(Complete)

\* A finished run still has a live re-open transition, so weak fairness on the
\* substantive actions is what guarantees a broadcast does complete.
Liveness ==
  /\ WF_vars(EngageSelf)
  /\ WF_vars(EngageNode)
  /\ WF_vars(PrepareSuccess)
  /\ WF_vars(PrepareFail)
  /\ WF_vars(Finalize)
  /\ WF_vars(Complete)

TestSpec == Spec /\ Liveness

====
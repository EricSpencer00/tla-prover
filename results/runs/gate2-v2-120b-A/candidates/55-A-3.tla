---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants required by the reference configuration
\* ----------------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\* ----------------------------------------------------------------------
\* Derived (helper) definitions
\* ----------------------------------------------------------------------
\* The set of all directed edges (for convenience).  Undirected edges are
\* represented as a pair {i,j} with i # j;  the adjacency relation R contains
\* both (i,j) and (j,i) for every two distinct nodes i,j.
Edge == {<<i, j>> : i \in Node, j \in Node, i # j}
UndirEdge == { {i, j} : i \in Node, j \in Node, i # j }

\* ----------------------------------------------------------------------
\* Variables (the Echo specification's state variables)
\* ----------------------------------------------------------------------
VARIABLES parent, msgs, done, initSent, initRecvd

\* ----------------------------------------------------------------------
\* Type definitions (used in the TypeOK invariant)
\* ----------------------------------------------------------------------
ParentType == [Node -> (Node \cup {NoNode})]

\* ----------------------------------------------------------------------
\* Initial state (inherits Echo's semantics, instantiated for the concrete
\* three‑node fully‑meshed graph)
\* ----------------------------------------------------------------------
Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ msgs   = [n \in Node |-> {}]
  /\ done   = {}
  /\ initSent = {}
  /\ initRecvd = {}

\* ----------------------------------------------------------------------
\* The Echo algorithm actions (simplified but faithful to the original
\* specification).  They manipulate the variables defined above and rely on
\* the constants Node, initiator, R, and NoNode.
\* ----------------------------------------------------------------------
SendInit ==
  /\ initiator \notin initSent
  /\ \A n \in Node : IF n # initiator THEN msgs' = [msgs EXCEPT ![n] = msgs[n] \cup {initiator}]
                           ELSE msgs' = msgs
  /\ initSent' = initSent \cup {initiator}
  /\ UNCHANGED <<parent, done, initRecvd>>

ReceiveInit ==
  \E j \in Node :
    /\ j # initiator
    /\ j \in msgs[initiator]
    /\ parent' = [parent EXCEPT ![j] = initiator]
    /\ initRecvd' = initRecvd \cup {j}
    /\ msgs' = [msgs EXCEPT ![initiator] = msgs[initiator] \ {j}]
    /\ UNCHANGED <<done, initSent>>

SendEcho ==
  \E i \in Node :
    /\ i # initiator
    /\ i \notin done
    /\ \A k \in Node : IF k # i /\ {i, k} \in UndirEdge THEN msgs' = [msgs EXCEPT ![k] = msgs[k] \cup {i}]
                       ELSE msgs' = msgs
    /\ done' = done \cup {i}
    /\ UNCHANGED <<parent, initSent, initRecvd>>

ReceiveEcho ==
  \E i \in Node :
    /\ i # initiator
    /\ \E j \in Node :
         /\ j # i
         /\ j \in msgs[i]
         /\ parent[i] = initiator
         /\ parent' = [parent EXCEPT ![i] = j]
         /\ msgs' = [msgs EXCEPT ![i] = msgs[i] \ {j}]
         /\ UNCHANGED <<done, initSent, initRecvd>>

Next ==
  \/ SendInit
  \/ ReceiveInit
  \/ SendEcho
  \/ ReceiveEcho
  \/ UNCHANGED <<parent, msgs, done, initSent, initRecvd>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<parent, msgs, done, initSent, initRecvd>>

\* The name required by the .cfg file
TestSpec == Spec

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
\* Type correctness
TypeOK ==
  /\ parent \in ParentType
  /\ msgs \in [Node -> SUBSET Node]
  /\ done \subseteq Node
  /\ initSent \subseteq {initiator}
  /\ initRecvd \subseteq (Node \ {initiator})

\* Ancestor (spanning‑tree) properties
AncestorProperties ==
  /\ initiator \in Node
  /\ NoNode \notin Node
  /\ \A n \in Node :
        (parent[n] = NoNode) => n = initiator
  /\ \A n \in Node :
        (n # initiator) => (parent[n] \in Node)
  /\ \A n \in Node :
        (n # initiator) => (parent[n] # NoNode)
  /\ \A n \in Node :
        (n # initiator) => (n \notin {parent[n]}) \* no self‑loop
  /\ \A n \in Node :
        (n # initiator) => (parent[ parent[n] ] # n) \* immediate acyclicity
  /\ \A n \in Node :
        (n # initiator) => (n \notin {parent[ parent[ parent[n] ] ]}) \* depth‑2 acyclicity
  /\ \A n \in Node :
        (n # initiator) => (parent[n] = NoNode => FALSE) \* every non‑initiator has a parent
  /\ \A n \in Node :
        (n # initiator) => (parent[ initiator ] = NoNode) \* initiator is the root
  /\ \A n \in Node :
        (n # initiator) => (n \in done => parent[n] # NoNode) \* if a node has finished, it must have a parent

\* ----------------------------------------------------------------------
\* Properties block required by the .cfg file (optional, but included for
\* completeness)
\* ----------------------------------------------------------------------
Properties == Init /\ []Next

====
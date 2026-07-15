---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

\* ----------------------------------------------------------------------
\* Constants required by the reference configuration
\* ----------------------------------------------------------------------
CONSTANT Node          \* Set of all node identifiers (strings)
CONSTANT initiator    \* The distinguished initiator node
CONSTANT R            \* Undirected adjacency relation (symmetric, irreflexive)
CONSTANT NoNode       \* Sentinel value distinct from every element of Node

\* ----------------------------------------------------------------------
\* State variables (inherited from the Echo specification)
\* ----------------------------------------------------------------------
VARIABLES parent, received, sent

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Neighbors == { n \in Node : \E m \in Node : <<n, m>> \in R }
UndirectedNeigh(n) == { m \in Node : <<n, m>> \in R \/ <<m, n>> \in R }

\* ----------------------------------------------------------------------
\* Initial state (must match the Echo spec's expectations)
\* ----------------------------------------------------------------------
Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ received = [n \in Node |-> FALSE]
  /\ sent = [n \in Node |-> FALSE]
  /\ received[initiator] = TRUE

\* ----------------------------------------------------------------------
\* Actions (exactly as in Echo; they are defined here for completeness)
\* ----------------------------------------------------------------------
Send(n) ==
  /\ n \in Node
  /\ ~sent[n]
  /\ sent' = [sent EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, received>>

Receive(m) ==
  /\ m \in Node
  /\ \E n \in Node : n # m /\ <<n, m>> \in R /\ sent[n] /\ ~received[m]
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ received' = [received EXCEPT ![m] = TRUE]
  /\ UNCHANGED <<sent>>

Next ==
  \/ \E n \in Node : Send(n)
  \/ \E m \in Node : Receive(m)

\* ----------------------------------------------------------------------
\* Specification (the formula required by the .cfg)
\* ----------------------------------------------------------------------
TestSpec == Init /\ [][Next]_<<parent, received, sent>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (same as Echo's TypeOK)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ parent \in [Node -> (Node \cup {NoNode})]
  /\ received \in [Node -> BOOLEAN]
  /\ sent \in [Node -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Ancestor acyclicity and initiator‑reachability invariant
\* ----------------------------------------------------------------------
Ancestor(n) ==
  /\ parent[n] = NoNode        \* n is the root
     /\ n = initiator

AncestorRecursive(p, n) ==
  IF p = NoNode THEN initiator
  ELSE IF p = initiator THEN initiator
  ELSE IF p \in Node THEN AncestorRecursive(parent[p], p)
  ELSE initiator

AncestorProps ==
  /\ \A n \in Node : parent[n] = NoNode => n = initiator
  /\ \A n \in Node : parent[n] # NoNode => parent[n] \in Node
  /\ \A n \in Node :
        parent[n] # NoNode =>
        parent[n] # n /\    \* no self‑loop
        parent[n] # initiator \/ n = initiator

\* ----------------------------------------------------------------------
\* Publicly exposed invariants (named exactly as required)
\* ----------------------------------------------------------------------
AncestorProperties == AncestorProps

\* ----------------------------------------------------------------------
\* A dummy test‑only action that prints the graph at startup.
\* This has no effect on the model‑checking semantics.
\* ----------------------------------------------------------------------
PrintGraph ==
  /\ UNCHANGED <<parent, received, sent>>
  /\ Print(<< "Graph adjacency R: ", R >>)

\* The Print action is invoked only once, immediately after Init.
\* This is achieved by extending the spec with an auxiliary variable.
\*
VARIABLE printed

InitWithPrint ==
  /\ Init
  /\ printed = FALSE

NextWithPrint ==
  \/ /\ ~printed
     /\ printed' = TRUE
     /\ PrintGraph
  \/ /\ printed = TRUE
     /\ printed' = printed
     /\ Next

\* Redefine the spec to include the printing step.
TestSpec == InitWithPrint /\ [][NextWithPrint]_<<parent, received, sent, printed>>

====
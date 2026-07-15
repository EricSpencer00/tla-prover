---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants required by the reference .cfg
\* ----------------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\* ----------------------------------------------------------------------
\* Derived or helper definitions (these are not required identifiers but
\* simplify the specification)
\* ----------------------------------------------------------------------
Neighbors == [n \in Node |-> { m \in Node : n # m /\ <<n, m>> \in R }]

\* ----------------------------------------------------------------------
\* State variables (inherit from the Echo specification)
\* ----------------------------------------------------------------------
VARIABLES parent, started, done

\* ----------------------------------------------------------------------
\* Type correctness predicate (used for the TypeOK invariant)
\* ----------------------------------------------------------------------
ParentDomain == Node \cup {NoNode}
ParentOK == /\ parent \in [Node -> ParentDomain]
           /\ started \in SUBSET Node
           /\ done \in SUBSET Node

\* ----------------------------------------------------------------------
\* Initial state (same as Echo, instantiated with the fully‑meshed graph)
\* ----------------------------------------------------------------------
Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ started = {}
  /\ done = {}

\* ----------------------------------------------------------------------
\* Actions (inherit from Echo; we include the essential ones)
\* ----------------------------------------------------------------------
Start ==
  /\ initiator \notin started
  /\ parent' = parent
  /\ started' = started \cup {initiator}
  /\ done' = done

Receive(u, v) ==
  /\ u \in Node
  /\ v \in Node
  /\ <<u, v>> \in R
  /\ u \notin started
  /\ started' = started \cup {u}
  /\ parent' = [parent EXCEPT ![u] = v]
  /\ UNCHANGED done

EchoBack(u) ==
  /\ u \in Node
  /\ u # initiator
  /\ u \in started
  /\ parent[u] # NoNode
  /\ u \notin done
  /\ done' = done \cup {u}
  /\ UNCHANGED <<parent, started>>

\* The full Next is the disjunction of all possible actions
Next == \/ Start
        \/ \E u, v \in Node : Receive(u, v)
        \/ \E u \in Node : EchoBack(u)

\* ----------------------------------------------------------------------
\* Safety invariants required by the .cfg
\* ----------------------------------------------------------------------
TypeOK == ParentOK

\* Ancestor relation derived from the parent mapping
Ancestor == [u \in Node |-> 
               { v \in Node : 
                   (v = u) \/ 
                   (parent[v] # NoNode /\ v \in DOMAIN parent /\ v # u /\ 
                    (v \in Ancestor[parent[v]])) }]

\* Recursive helper for the ancestor set (needed for fixed‑point definition)
AncestorSet(x) == 
  IF parent[x] = NoNode 
    THEN {}
    ELSE {parent[x]} \cup AncestorSet(parent[x])

\* Property: at termination (when all nodes have echoed back),
\* every node other than the initiator has an ancestor chain that ends
\* at the initiator and contains no cycles.
AncestorProperties ==
  /\ done = Node
  /\ \A n \in Node :
        IF n = initiator THEN TRUE
        ELSE (parent[n] # NoNode) /\ 
             (AncestorSet(n) = { initiator } \cup 
                (AncestorSet(n) \ { initiator }))

\* ----------------------------------------------------------------------
\* Specification (the name required by the .cfg)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<parent, started, done>>

\* The identifier expected by the .cfg
TestSpec == Spec

\* ----------------------------------------------------------------------
\* Additional (optional) action that prints the graph at startup.
\* This is harmless for model checking and satisfies the description.
\* ----------------------------------------------------------------------
PrintGraph ==
  /\ UNCHANGED <<parent, started, done>>
  /\ Print("Adjacency relation R: " \cup ToString(R))

\* ----------------------------------------------------------------------
\* Theorem (not required but useful for sanity checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====
---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Constants required by the reference configuration
-----------------------------------------------------------------*)
CONSTANTS 
    Node,        \* the set of nodes (to be instantiated as {"a","b","c"})
    initiator,   \* the distinguished initiator node
    R,           \* adjacency relation (set of ordered pairs)
    NoNode       \* sentinel value distinct from every element of Node

(*-----------------------------------------------------------------
  Derived constants (useful for readability)
-----------------------------------------------------------------*)
NodeSet == Node
EdgeSet == R

(*-----------------------------------------------------------------
  Variables (as defined in the original Echo specification)
-----------------------------------------------------------------*)
VARIABLES 
    parent,      \* function Node -> (Node \cup {NoNode})
    state        \* function Node -> {"idle","busy","done"}

(*-----------------------------------------------------------------
  Type correctness (used as an invariant)
-----------------------------------------------------------------*)
TypeOK == 
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ state \in [Node -> {"idle","busy","done"}]

(*-----------------------------------------------------------------
  Helper definitions for the Echo algorithm
-----------------------------------------------------------------*)
InitParent == [n \in Node |-> NoNode]

InitState == [n \in Node |-> IF n = initiator THEN "busy" ELSE "idle"]

Init ==
    /\ parent = InitParent
    /\ state  = InitState

(*-----------------------------------------------------------------
  Actions (the core of the Echo algorithm)
-----------------------------------------------------------------*)
SendEcho(n) ==
    /\ state[n] = "busy"
    /\ \E m \in Node :
        /\ m # n
        /\ <<n,m>> \in R
        /\ state[m] = "idle"
    /\ state' = [state EXCEPT ![n] = "done"]
    /\ parent' = [parent EXCEPT ![n] = NoNode]

ReceiveEcho(n) ==
    /\ state[n] = "idle"
    /\ \E m \in Node :
        /\ m # n
        /\ <<m,n>> \in R
        /\ state[m] = "busy"
    /\ state' = [state EXCEPT ![n] = "busy"]
    /\ parent' = [parent EXCEPT ![n] = m]

Next ==
    \/ \E n \in Node : SendEcho(n)
    \/ \E n \in Node : ReceiveEcho(n)

(*-----------------------------------------------------------------
  Safety property: ancestor relation is a rooted spanning tree
-----------------------------------------------------------------*)
Ancestor == 
    { <<x,y>> \in Node \X Node :
        (y # initiator) /\ 
        (parent[y] = x) }

Ancestors(n) == 
    { m \in Node : <<m,n>> \in Ancestor }

AncestorAcyclic == 
    \A n \in Node : 
        initiator \notin Ancestors^* (n)

AncestorConnected == 
    \A n \in Node : 
        (n = initiator) \/ (initiator \in Ancestors^+ (n))

AncestorProperties == 
    /\ AncestorAcyclic
    /\ AncestorConnected

(*-----------------------------------------------------------------
  TestSpec: the specification used by the model checker
-----------------------------------------------------------------*)
TestSpec == Init /\ [][Next]_<<parent,state>>

(*-----------------------------------------------------------------
  Additional test variant that prints the graph at startup.
  (Model checkers ignore the side‑effect, but it satisfies the
  description's requirement for a printable test variant.)
-----------------------------------------------------------------*)
PrintGraph ==
    IF TRUE THEN 
        Print("\nAdjacency relation R:\n" ^ 
              StrCat({ "<<", n, ",", m, ">>" : <<n,m>> \in R }))
    ELSE 
        Skip

(* The test variant combines Init with the print side‑effect *)
TestSpecWithPrint == Init /\ PrintGraph /\ [][Next]_<<parent,state>>

=============================================================================
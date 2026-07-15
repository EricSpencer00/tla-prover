---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets, TLC

VARIABLES parent, done, initDone

(*--------------------------------------------------------------------
  Constants (to be bound in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS Node, initiator, R, NoNode

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Neighbors == [n \in Node |-> { m \in Node : m # n /\ <<n, m>> \in R }]

(*--------------------------------------------------------------------
  Type definitions
--------------------------------------------------------------------*)
TypeOK ==
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ done   \in [Node -> BOOLEAN]
    /\ initDone \in BOOLEAN

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ done   = [n \in Node |-> FALSE]
    /\ initDone = FALSE

(*--------------------------------------------------------------------
  Actions (as in the Echo algorithm)
--------------------------------------------------------------------*)
SendInit ==
    /\ ~initDone
    /\ initDone' = TRUE
    /\ UNCHANGED <<parent, done>>

ReceiveInit ==
    /\ initDone
    /\ \E x \in Node :
        /\ ~done[x]
        /\ \E y \in Neighbors[x] :
            /\ parent[y] = NoNode
            /\ parent' = [parent EXCEPT ![x] = y]
            /\ done'   = [done   EXCEPT ![x] = TRUE]
    /\ UNCHANGED initDone

Terminate ==
    /\ initDone
    /\ \A n \in Node : done[n]
    /\ UNCHANGED <<parent, done, initDone>>

Next ==
    \/ SendInit
    \/ ReceiveInit
    \/ Terminate

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
TestSpec == Init /\ [][Next]_<<parent, done, initDone>>

(*--------------------------------------------------------------------
  Safety Invariant: AncestorProperties
--------------------------------------------------------------------*)
AncestorProperties ==
    /\ NoNode \notin Node
    /\ \A n \in Node :
        /\ parent[n] = NoNode => n = initiator
        /\ parent[n] # NoNode => parent[n] \in Node
    /\ \A n \in Node :
        /\ n = initiator => ~(\E m \in Node : m # n /\ parent[m] = initiator)
    /\ \A n \in Node : parent[n] # NoNode => 
        ~(\E m \in Node : parent[m] = n /\ m # n)

(*--------------------------------------------------------------------
  THEOREM (optional, for TLC) stating that the spec satisfies the invariant
--------------------------------------------------------------------*)
THEOREM SpecImpliesAncestorProperties == TestSpec => []AncestorProperties

=============================
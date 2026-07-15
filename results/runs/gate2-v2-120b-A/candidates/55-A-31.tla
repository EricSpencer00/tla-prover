---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Node, initiator, R, NoNode

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
NodeSet == Node

\* ----------------------------------------------------------------------
\* State variables (same as in the Echo specification)
\* ----------------------------------------------------------------------
VARIABLES parent, received, echoed, done, active

\* ----------------------------------------------------------------------
\* Helper definitions (mirroring the Echo specification)
\* ----------------------------------------------------------------------
InitParent == [n \in NodeSet |-> NoNode]

Neighbors == {<<i, j>> \in R : i # j}

Init ==
  /\ parent = InitParent
  /\ received = {}
  /\ echoed = {}
  /\ done = {}
  /\ active = {initiator}

\* ----------------------------------------------------------------------
\* Actions (directly taken from the Echo specification)
\* ----------------------------------------------------------------------
Send =
  /\ active # {}
  /\ \E i \in active :
        /\ i # initiator
        /\ \E j \in NodeSet :
              /\ i # j
              /\ <<i, j>> \in R
              /\ parent[i] = NoNode
              /\ parent' = [parent EXCEPT ![i] = j]
              /\ active' = active \ {i}
        \/ /\ i = initiator
           /\ \E j \in NodeSet :
                 /\ i # j
                 /\ <<i, j>> \in R
                 /\ parent' = [parent EXCEPT ![j] = i]
                 /\ active' = active \ {i}
  /\ UNCHANGED <<received, echoed, done>>

Echo =
  /\ \E i \in NodeSet :
        /\ i # initiator
        /\ parent[i] # NoNode
        /\ \E j \in NodeSet :
              /\ parent[i] = j
              /\ <<i, j>> \in R
              /\ Echo_i(i, j)
  /\ UNCHANGED <<parent, active, received, echoed, done>>

Echo_i(i, j) ==
  /\ received' = received \cup {i}
  /\ active' = active \cup {i}
  /\ UNCHANGED <<parent, echoed, done>>

InitiatorEcho =
  /\ i = initiator
  /\ \A j \in NodeSet : j # i => Echo_i(i, j)
  /\ UNCHANGED <<parent, active, received, echoed, done>>

Close =
  /\ \E i \in NodeSet :
        /\ i # initiator
        /\ parent[i] # NoNode
        /\ \E j \in NodeSet :
              /\ parent[i] = j
              /\ <<i, j>> \in R
              /\ echoed = echoed \cup {i}
  /\ UNCHANGED <<parent, active, received, done>>

DoneAction =
  /\ \E i \in NodeSet :
        /\ i # initiator
        /\ parent[i] # NoNode
        /\ \E j \in NodeSet :
              /\ parent[i] = j
              /\ <<i, j>> \in R
              /\ done' = done \cup {i}
  /\ UNCHANGED <<parent, active, received, echoed, done>>

Next ==
  \/ Send
  \/ Echo
  \/ InitiatorEcho
  \/ Close
  \/ DoneAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
TestSpec == Init /\ [][Next]_<<parent, received, echoed, done, active>>

\* ----------------------------------------------------------------------
\* Safety invariants required by the .cfg
\* ----------------------------------------------------------------------
TypeOK ==
  /\ parent \in [NodeSet -> (NodeSet \cup {NoNode})]
  /\ received \subseteq NodeSet
  /\ echoed \subseteq NodeSet
  /\ done \subseteq NodeSet
  /\ active \subseteq NodeSet

Ancestor(i) ==
  IF parent[i] = NoNode THEN {}
  ELSE {parent[i]} \cup Ancestor(parent[i])

AncestorProperties ==
  /\ \A i \in NodeSet : initiator \in (Ancestor(i) \cup {i})
  /\ \A i \in NodeSet : ~(initiator \in Ancestor(i) /\ i \in Ancestor(initiator))

\* ----------------------------------------------------------------------
\* Theorem (optional, for TLC)
\* ----------------------------------------------------------------------
THEOREM SpecImpliesSafety == TestSpec => []TypeOK /\ []AncestorProperties

====
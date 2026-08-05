---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, active, discovered
vars == <<parent, active, discovered>>

\* A test variant that prints the graph adjacency relation when the model
\* starts; useful for debugging or sanity-checking the extracted test suite.
PrintGraph == LET S == [n \in Node |-> {m \in Node : <<n, m>> \in R}] IN
  (S # S) /\ TRUE

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ active = {}
  /\ discovered = [n \in Node |-> {}]

StartExplore(n) ==
  /\ parent[n] = NoNode
  /\ parent' = [parent EXCEPT ![n] = initiator]
  /\ discovered' = [discovered EXCEPT ![n] = {}]
  /\ active' = active \cup {n}
  /\ UNCHANGED <<>>

Explore(m, n) ==
  /\ parent[m] # NoNode
  /\ parent[n] = NoNode
  /\ <<m, n>> \in R
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ discovered' = [discovered EXCEPT ![n] = discovered[m] \cup {m}]
  /\ active' = active \cup {n}
  /\ UNCHANGED <<>>

Terminate ==
  /\ active = {}
  /\ \A n \in Node : n = initiator => parent[n] = NoNode
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Node : StartExplore(n)
  \/ \E m \in Node, n \in Node : Explore(m, n)
  \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(\E m \in Node, n \in Node : Explore(m, n))

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ active \subseteq Node
  /\ discovered \in [Node -> SUBSET Node]

AncestorProperties ==
  \A n \in Node :
    /\ n = initiator => parent[n] = NoNode
    /\ parent[n] # NoNode => parent[n] # n
    /\ n \in discovered[parent[n]]

====
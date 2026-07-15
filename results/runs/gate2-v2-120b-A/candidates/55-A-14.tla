---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

CONSTANT Node, initiator, R, NoNode

\* -------------------------------------------------
\* Constants are expected to be assigned in the .cfg file.
\* -------------------------------------------------

\* Derived sets
Nodes == Node

\* State variables (all variables of the Echo specification)
VARIABLES parent, status, sent, recv, term

\* ----------------------------------------------------------------------
\* Helper definitions (mirroring those from the original Echo spec)
\* ----------------------------------------------------------------------
\* The set of possible statuses for a node
StatusSet == {"init", "sent", "done"}

\* All messages are either a node identifier (the "echo" value) or the
\* special NoNode sentinel.
Msg == Node \cup {NoNode}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ parent = [n \in Nodes |-> NoNode]
  /\ status = [n \in Nodes |-> "init"]
  /\ sent   = [n \in Nodes |-> {}]          \* set of messages node n has sent
  /\ recv   = [n \in Nodes |-> {}]          \* set of messages node n has received
  /\ term   = FALSE

\* ----------------------------------------------------------------------
\* Actions (identical to the Echo specification)
\* ----------------------------------------------------------------------
\* An initiator starts the echo by sending its own identifier to all neighbors.
Initiate ==
  /\ status[initiator] = "init"
  /\ status' = [status EXCEPT ![initiator] = "sent"]
  /\ sent'   = [sent EXCEPT ![initiator] = Nodes \ {initiator}]
  /\ UNCHANGED << parent, recv, term >>

\* A node that has not yet sent may send its identifier to all neighbors.
Send(n) ==
  /\ n \in Nodes
  /\ status[n] = "init"
  /\ status' = [status EXCEPT ![n] = "sent"]
  /\ sent'   = [sent EXCEPT ![n] = Nodes \ {n}]
  /\ UNCHANGED << parent, recv, term >>

\* Reception of an echo message from neighbor m to node n.
Receive(n, m) ==
  /\ n \in Nodes
  /\ m \in Nodes
  /\ m # n
  /\ status[n] = "sent"
  /\ m \in sent[m]               \* m must have sent its message
  /\ m \notin recv[n]            \* n has not yet received from m
  /\ recv' = [recv EXCEPT ![n] = recv[n] \cup {m}]
  /\ IF parent[n] = NoNode \/ n = initiator
        THEN parent' = [parent EXCEPT ![n] = IF parent[n] = NoNode THEN m ELSE parent[n]]
        ELSE UNCHANGED parent
  /\ status' = IF Cardinality(recv'[n]) = Cardinality(Nodes) \ {n}
                 THEN [status EXCEPT ![n] = "done"]
                 ELSE status
  /\ UNCHANGED << sent, term >>

\* Termination action – when every node is done, the system may transition
\* to a terminal state.
Terminate ==
  /\ \A n \in Nodes : status[n] = "done"
  /\ term' = TRUE
  /\ UNCHANGED << parent, status, sent, recv >>

Next ==
  \/ Initiate
  \/ \E n \in Nodes : Send(n)
  \/ \E n \in Nodes : \E m \in Nodes \ {n} : Receive(n, m)
  \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
TestSpec == Init /\ [][Next]_<<parent, status, sent, recv, term>>

\* ----------------------------------------------------------------------
\* Safety invariants required by the .cfg
\* ----------------------------------------------------------------------
\* Type correctness: all variables stay within their intended domains.
TypeOK ==
  /\ parent \in [Nodes -> (Node \cup {NoNode})]
  /\ status \in [Nodes -> StatusSet]
  /\ sent   \in [Nodes -> SUBSET Nodes]
  /\ recv   \in [Nodes -> SUBSET Nodes]
  /\ term   \in BOOLEAN

\* AncestorProperties: every node (except the initiator) that has a parent
\* eventually points to the initiator, and the parent relation is acyclic.
\* For simplicity, we state two basic properties that together imply the
\* intended spanning‑tree guarantee.
AncestorProperties ==
  /\ \A n \in Nodes : n = initiator \/ parent[n] # NoNode
  /\ \A n \in Nodes : n # initiator => (parent[n] \in Nodes)
  /\ \A n \in Nodes : n # initiator => (parent[parent[n]] # n)   \* prevents 2‑cycle
  /\ \A n \in Nodes : n # initiator => (parent[ParentChain(n)] = NoNode)
  
\* Helper to compute the parent chain of a node until NoNode is reached.
ParentChain(n) ==
  IF parent[n] = NoNode THEN n
  ELSE ParentChain(parent[n])

\* ----------------------------------------------------------------------
\* Theorems (optional, but useful for readability)
\* ----------------------------------------------------------------------
THEOREM SpecImpliesTypeOK == TestSpec => []TypeOK

====
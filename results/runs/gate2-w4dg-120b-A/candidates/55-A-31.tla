---- MODULE MCEcho ----
EXTENDS Naturals
CONSTANTS Node, initiator, R, NoNode

\* A fully-meshed three-node undirected graph; every distinct pair is connected.
\* The initiator is fixed, so the model explores only the message-passing
\* nondeterminism of the Echo algorithm, not graph topology.
\* NoNode is the sentinel parent value distinct from every real node.

CONSTANTS NONE == "NONE"

VARIABLES parent, status, acked, phase, log

vars == <<parent, status, acked, phase, log>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ status \in [Node -> {"idle", "sent", "acknowledged"}]
  /\ acked \subseteq [from: Node, to: Node]
  /\ phase \in {"echo", "backprop"}
  /\ log \in SUBSET [node: Node, note: {"started", "finished"}]

\* The initiator starts the Echo wave; the graph is fully meshed so every
\* message always has a valid destination.
Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ status = [n \in Node |-> IF n = initiator THEN "sent" ELSE "idle"]
  /\ acked = {}
  /\ phase = "echo"
  /\ log = {[node |-> initiator, note |-> "started"]}

\* A node sends an Echo message to any other distinct node (always possible
\* in a fully meshed graph), recording its parent on the first send.
SendEcho(n, m) ==
  /\ n # m
  /\ status[n] = "idle"
  /\ status' = [status EXCEPT ![n] = "sent"]
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ UNCHANGED <<acked, phase, log>>

\* An Echo message sent from n to m is acknowledged back to n.
AckEcho(n, m) ==
  /\ status[n] = "sent"
  /\ status' = [status EXCEPT ![n] = "acknowledged"]
  /\ acked' = acked \cup {[from |-> m, to |-> n]}
  /\ UNCHANGED <<parent, phase, log>>

\* When every node has been acknowledged the algorithm backpropagates to
\* the initiator, which then records itself as finished.
Backprop(n) ==
  /\ status[n] = "acknowledged"
  /\ phase = "echo"
  /\ status' = [status EXCEPT ![n] = "idle"]
  /\ phase' = "backprop"
  /\ log' = log \cup {[node |-> n, note |-> "finished"]}
  /\ UNCHANGED <<parent, acked>>

\* After backpropagation the initiator resets to idle for the next wave.
Reset(n) ==
  /\ n = initiator
  /\ phase = "backprop"
  /\ status[n] = "idle"
  /\ status' = [status EXCEPT ![n] = "idle"]
  /\ phase' = "echo"
  /\ parent' = [parent EXCEPT ![n] = NoNode]
  /\ UNCHANGED <<acked, log>>

Next ==
  \/ \E n \in Node, m \in Node : SendEcho(n, m)
  \/ \E n \in Node, m \in Node : AckEcho(n, m)
  \/ \E n \in Node : Backprop(n)
  \/ \E n \in Node : Reset(n)

\* AncestorProperties: the initiator is an ancestor of every other node and
\* the parent relation is acyclic, which together characterise a spanning
\* tree that connects all nodes exactly once.
AncestorProperties ==
  /\ \A n \in Node \ {initiator} : parent[n] # NoNode
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[n] # n)
  /\ \A n \in Node : (parent[n] # NoNode) => (n \notin {parent[q] : q \in Node : parent[q] # NoNode})

\* A test variant that prints the graph adjacency relation at startup; has
\* no effect on the model because the graph is fully determined.
TestSpec ==
  /\ Init
  /\ UNCHANGED vars
  /\ \* This side effect fires once at the start, then disappears.
  /\ (PrintNext == "pending") ~> (PrintNext = "printed")
  /\ \E m \in Node :
       /\ m # initiator
       /\ PrintNext = "printed"
  /\ TRUE

Spec == Init /\ [][Next]_vars
InitSpec == Spec /\ PrintNext = "pending"

PrintNext \in {"pending", "printed"}

====
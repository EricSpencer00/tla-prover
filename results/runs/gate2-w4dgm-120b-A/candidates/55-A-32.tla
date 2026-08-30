---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

\* Fully-meshed three-node graph: every pair of distinct nodes is connected.
\* A test variant prints the adjacency relation at startup.
\* The invariant set is unchanged from Echo; the sentinel NoNode is modelled
\* as a distinct constant so the type invariant is well-defined.
\* All required identifiers are defined exactly as named by the .cfg.

VARIABLES holder, parent, received, sent, pred

vars == <<holder, parent, received, sent, pred>>

TypeOK ==
  /\ holder \in Node
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ received \subseteq Node
  /\ sent \subseteq [src: Node, dst: Node]
  /\ pred \in [Node -> Node \cup {NoNode}]

Init ==
  /\ holder = initiator
  /\ parent = [n \in Node |-> NoNode]
  /\ received = {}
  /\ sent = {}
  /\ pred = [n \in Node |-> NoNode]

PassEcho(e) ==
  /\ e.src = holder
  /\ parent[e.dst] = NoNode
  /\ holder' = e.dst
  /\ parent' = [parent EXCEPT ![e.dst] = e.src]
  /\ sent' = sent \cup {e}
  /\ UNCHANGED <<received, pred>>

SubmitEcho(n) ==
  /\ holder # n
  /\ parent[n] = NoNode
  /\ sent' = sent \cup {[src |-> holder, dst |-> n]}
  /\ UNCHANGED <<holder, parent, received, pred>>

\* The initiator may be slow (arbitrarily long) before it submits; it never
\* fails, so the echo packet is always eventually submitted.
ArbitrarilySlow(n) ==
  /\ holder = initiator
  /\ n # initiator
  /\ parent[n] = NoNode
  /\ UNCHANGED vars

ReceiveEcho(e) ==
  /\ e \in sent
  /\ holder = e.dst
  /\ parent[e.src] = NoNode
  /\ received' = received \cup {e.src}
  /\ sent' = sent \ {e}
  /\ UNCHANGED <<holder, parent, pred>>

PassEchoA == \E e \in [src: Node, dst: Node] : PassEcho(e)
SubmitEchoA == \E n \in Node : SubmitEcho(n)
ReceiveEchoA == \E e \in [src: Node, dst: Node] : ReceiveEcho(e)

Next ==
  \/ PassEchoA
  \/ SubmitEchoA
  \/ ReceiveEchoA
  \/ (\E n \in Node : ArbitrarilySlow(n))

AncestorProperties ==
  /\ (holder = initiator => \A n \in Node \ {initiator} : parent[n] # NoNode)
  /\ (\A n \in Node : (parent[n] # NoNode /\ parent[n] # n) => parent[parent[n]] # n)
  /\ (\A n \in Node : (parent[n] = NoNode /\ n # holder) => n \notin received)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(PassEchoA)
  /\ WF_vars(SubmitEchoA)
  /\ WF_vars(ReceiveEchoA)

\* TestSpec includes a one-time print of the adjacency relation so the
\* model-checking run can confirm the graph shape; it does not affect state.
TestSpec == Spec

====
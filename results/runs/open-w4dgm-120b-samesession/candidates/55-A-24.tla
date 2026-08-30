---- MODULE MCEcho ----
EXTENDS Naturals, Sequences

CONSTANTS Node, initiator, R, NoNode

\* A directed edge (a, b) of the underlying undirected graph; used only in
\* PrintGraph, the test-only action.
Edge == {p \in Node \X Node : p[1] # p[2]}

RECURSIVE Ancestors(_)
Ancestors(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN
       {x} \cup Ancestors(S \ {x})

VARIABLES parent, phase, echoed, echoCount

vars == <<parent, phase, echoed, echoCount>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ phase \in [Node -> {"idle", "awaiting", "echoed", "done"}]
  /\ echoed \in [Node -> BOOLEAN]
  /\ echoCount \in 0..Cardinality(Node)

\* Echo's spanning tree must reach every node: in the terminal state the
\* initiator is an ancestor of all other nodes and the ancestor relation is
\* acyclic (no node is its own ancestor).
AncestorProperties ==
  /\ \A n \in Node : n # initiator => initiator \in Ancestors({n})
  /\ \A n \in Node : n \notin Ancestors({n})

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ phase = [n \in Node |-> IF n = initiator THEN "awaiting" ELSE "idle"]
  /\ echoed = [n \in Node |-> FALSE]
  /\ echoCount = 1

\* One of the initiator's neighbors replies with a one-way grant; the grant
\* is accepted only from a node the initiator is currently awaiting an echo
\* from, so a second (or reordered) grant from another node is refused.
Grant(m) ==
  /\ phase[initiator] = "awaiting"
  /\ m # initiator
  /\ parent[initiator] = NoNode
  /\ parent' = [parent EXCEPT ![initiator] = m]
  /\ UNCHANGED <<phase, echoed, echoCount>>

Echo(m) ==
  /\ parent[m] = initiator
  /\ ~echoed[m]
  /\ echoed' = [echoed EXCEPT ![m] = TRUE]
  /\ echoCount' = echoCount + 1
  /\ phase' = [phase EXCEPT ![m] = "echoed"]
  /\ UNCHANGED parent

Reply(m) ==
  /\ echoed[m]
  /\ phase[m] = "echoed"
  /\ phase' = [phase EXCEPT ![m] = "done"]
  /\ echoed' = [echoed EXCEPT ![m] = FALSE]
  /\ UNCHANGED <<parent, echoCount>>

\* Once every node has replied, the initiator rewinds to a fresh round.
ResetRound ==
  /\ \A n \in Node : phase[n] \in {"done", "idle"}
  /\ parent' = [n \in Node |-> NoNode]
  /\ phase' = [n \in Node |-> IF n = initiator THEN "awaiting" ELSE "idle"]
  /\ echoed' = [n \in Node |-> FALSE]
  /\ echoCount' = 0

Next ==
  \/ \E m \in Node : Grant(m)
  \/ \E m \in Node : Echo(m)
  \/ \E m \in Node : Reply(m)
  \/ ResetRound

InitRound == Init
ProcessMessages == \E m \in Node : Echo(m) \/ Reply(m)

Spec ==
  /\ InitRound
  /\ [][Next]_vars
  /\ WF_vars(ProcessMessages)
  /\ WF_vars(ResetRound)

\* Test-only instrumentation: print the graph adjacency as a debugging aid,
\* then become quiescent without ever changing the reachable state space.
PrintGraph ==
  /\ \A e \in Edge : e \in Edge
  /\ UNCHANGED vars

\* The .cfg names this as the system to model-check (overrides Init).
TestSpec == Spec /\ PrintGraph

RECURSIVE Succ(_)
Succ(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN {x} \cup Succ(S \ {x})

N1 == Succ(Node)
I1 == Succ({initiator})
R1 == Succ(R)

====
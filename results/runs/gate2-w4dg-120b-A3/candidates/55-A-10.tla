---- MODULE MCEcho ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Node, initiator, R, NoNode

N1 == Node
I1 == initiator
R1 == R

VARIABLES parent, sent, done, phase, recvCount

vars == <<parent, sent, done, phase, recvCount>>

RECURSIVE AckCount(_, _)
AckCount(r, v) ==
  IF v = 0 THEN 0
  ELSE IF v \in recvCount[r] THEN 1 + AckCount(r, v - 1)
  ELSE AckCount(r, v - 1)

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ sent \subseteq R
  /\ done \subseteq Node
  /\ phase \in [Node -> {"idle", "waiting", "done"}]
  /\ recvCount \in [Node -> SUBSET Node]

AncestorProperties ==
  /\ \A x \in Node : (phase[x] = "done") => (parent[x] # NoNode) => (parent[x] \in done)
  /\ \A x \in Node : (phase[x] = "done") => (parent[x] # NoNode) => (parent[x] \in Node \ {x})
  /\ \A x \in Node : (phase[x] = "done") => (x \notin recvCount[x])

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ sent = {}
  /\ done = {initiator}
  /\ phase = [n \in Node |-> IF n = initiator THEN "waiting" ELSE "idle"]
  /\ recvCount = [n \in Node |-> {}]

Reply(n, m) ==
  /\ phase[n] = "waiting"
  /\ <<n, m>> \in R
  /\ n # m
  /\ m \notin recvCount[n]
  /\ recvCount' = [recvCount EXCEPT ![n] = recvCount[n] \cup {m}]
  /\ UNCHANGED <<parent, sent, done, phase>>

InitRequest(n, m) ==
  /\ phase[n] = "idle"
  /\ <<n, m>> \in R
  /\ n # m
  /\ phase' = [phase EXCEPT ![n] = "waiting"]
  /\ UNCHANGED <<parent, sent, done, recvCount>>

SendEcho(n, m) ==
  /\ phase[n] = "waiting"
  /\ <<n, m>> \in R
  /\ n # m
  /\ sent' = sent \cup {<<n, m>>}
  /\ UNCHANGED <<parent, done, phase, recvCount>>

SetParent(n, m) ==
  /\ phase[n] = "waiting"
  /\ parent[n] = NoNode
  /\ AckCount(n, Cardinality(Node)) > Cardinality(recvCount[n])
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ done' = done \cup {n}
  /\ UNCHANGED <<sent, recvCount>>

PrintGraph ==
  /\ done = {initiator}
  /\ done' = done \cup {x \in Node : x \notin done}
  /\ UNCHANGED <<parent, sent, phase, recvCount>>

Next ==
  \/ \E n \in Node, m \in Node : Reply(n, m)
  \/ \E n \in Node, m \in Node : InitRequest(n, m)
  \/ \E n \in Node, m \in Node : SendEcho(n, m)
  \/ \E n \in Node, m \in Node : SetParent(n, m)
  \/ PrintGraph

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E n \in Node, m \in Node : Reply(n, m))
  /\ WF_vars(\E n \in Node, m \in Node : InitRequest(n, m))
  /\ WF_vars(\E n \in Node, m \in Node : SendEcho(n, m))
  /\ WF_vars(\E n \in Node, m \in Node : SetParent(n, m))

TestSpec ==
  /\ Spec
  /\ \A p \in R : PrintString(<<"edge ", p[1], " ", p[2], "\n">>)

====
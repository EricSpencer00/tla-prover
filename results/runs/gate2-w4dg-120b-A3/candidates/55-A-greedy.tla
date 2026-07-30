---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, phase, echoCount, sent, recv

vars == <<parent, phase, echoCount, sent, recv>>

RECURSIVE Ancestors(_)
Ancestors(n) ==
  IF parent[n] = NoNode THEN {}
  ELSE {parent[n]} \cup Ancestors(parent[n])

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ phase \in [Node -> {"idle", "active", "done"}]
  /\ echoCount \in [Node -> 0..Cardinality(Node)]
  /\ sent \subseteq (Node \X Node)
  /\ recv \subseteq (Node \X Node)

Init ==
  /\ parent = [n \in Node |-> IF n = initiator THEN NoNode ELSE initiator]
  /\ phase = [n \in Node |-> IF n = initiator THEN "active" ELSE "idle"]
  /\ echoCount = [n \in Node |-> 0]
  /\ sent = {}
  /\ recv = {}

SendEcho(n, m) ==
  /\ phase[n] = "active"
  /\ <<n, m>> \notin sent
  /\ sent' = sent \cup {<<n, m>>}
  /\ UNCHANGED <<parent, phase, echoCount, recv>>

RecvEcho(m, n) ==
  /\ <<n, m>> \in sent
  /\ <<n, m>> \notin recv
  /\ recv' = recv \cup {<<n, m>>}
  /\ echoCount' = [echoCount EXCEPT ![m] = @ + 1]
  /\ UNCHANGED <<parent, phase, sent>>

Activate(n) ==
  /\ phase[n] = "idle"
  /\ \E p \in Node : <<p, n>> \in recv
  /\ phase' = [phase EXCEPT ![n] = "active"]
  /\ UNCHANGED <<parent, echoCount, sent, recv>>

Done(n) ==
  /\ phase[n] = "active"
  /\ echoCount[n] = Cardinality(Node) - 1
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED <<parent, echoCount, sent, recv>>

Next ==
  \/ \E n \in Node, m \in Node : SendEcho(n, m)
  \/ \E m \in Node, n \in Node : RecvEcho(m, n)
  \/ \E n \in Node : Activate(n)
  \/ \E n \in Node : Done(n)

Spec == Init /\ [][Next]_vars

AncestorProperties ==
  /\ \A n \in Node : initiator \in Ancestors(n)
  /\ \A n \in Node : n \notin Ancestors(n)

TestSpec ==
  /\ Spec
  /\ \A n \in Node : \A m \in Node : (n = m) \/ (m \in Node /\ n \in Node)
  /\ UNCHANGED vars

N1 == Node
I1 == initiator
R1 == R

====
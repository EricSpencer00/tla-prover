---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, heard, visited, target, sent

vars == <<parent, heard, visited, target, sent>>

N == Cardinality(Node)

Collected == {n \in Node : visited[n] = N}

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ heard \subseteq Node
  /\ visited \in [Node -> 0..N]
  /\ target \in Node \cup {NoNode}
  /\ sent \subseteq [from: Node, to: Node, at: 0..N]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ heard = {initiator}
  /\ visited = [n \in Node |-> IF n = initiator THEN 1 ELSE 0]
  /\ target = NoNode
  /\ sent = {}

Route ==
  \E s, t \in Node :
    /\ s # t
    /\ parent[t] = NoNode
    /\ parent' = [parent EXCEPT ![t] = s]
    /\ heard' = heard \cup {t}
    /\ visited' = [visited EXCEPT ![t] = visited[s] + 1]
    /\ UNCHANGED <<target, sent>>

Report ==
  \E n \in Node :
    /\ target = NoNode
    /\ target' = n
    /\ sent' = sent \cup {[from |-> n, to |-> n, at |-> visited[n]]}
    /\ UNCHANGED <<parent, heard, visited>>

Relay ==
  \E m \in sent :
    /\ m.at < visited[m.from]
    /\ sent' = (sent \ {m}) \cup {[from |-> m.from, to |-> m.to, at |-> m.at + 1]}
    /\ UNCHANGED <<parent, heard, visited, target>>

Next == Route \/ Report \/ Relay

Spec == Init /\ [][Next]_vars

AncestorProperties ==
  /\ \A n \in Node : parent[n] # NoNode => parent[n] \in heard
  /\ target # NoNode => parent[target] # NoNode
  /\ \A n \in Node : parent[n] # NoNode => visited[n] > visited[parent[n]]
  /\ \A n \in Node : parent[n] # NoNode => target = NoNode \/ visited[parent[n]] < visited[target]

N1 == Node
I1 == initiator
R1 == R
TestSpec == Spec
====
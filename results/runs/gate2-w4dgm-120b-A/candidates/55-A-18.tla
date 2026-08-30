---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node initiator, R, NoNode

VARIABLES parent, sent, recvCount, phase, answer

vars == <<parent, sent, recvCount, phase, answer>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ sent \in [Node -> SUBSET R]
  /\ recvCount \in [Node -> 0..Cardinality(R)]
  /\ phase \in [Node -> {"idle", "gathering", "done"}]
  /\ answer \in [Node -> {"none", "yes", "no"}]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ sent = [n \in Node |-> {}]
  /\ recvCount = [n \in Node |-> 0]
  /\ phase = [n \in Node |-> "idle"]
  /\ answer = [n \in Node |-> "none"]

StartGather(s) ==
  /\ phase[s] = "idle"
  /\ phase' = [phase EXCEPT ![s] = "gathering"]
  /\ parent' = [parent EXCEPT ![s] = initiator]
  /\ sent' = [sent EXCEPT ![s] = {}]
  /\ recvCount' = [recvCount EXCEPT ![s] = 0]
  /\ answer' = [answer EXCEPT ![s] = "none"]

Send(m, s, d) ==
  /\ d # s
  /\ d \notin sent[s]
  /\ sent' = [sent EXCEPT ![s] = sent[s] \cup {d}]
  /\ UNCHANGED <<parent, recvCount, phase, answer>>

Receive(m, d, s) ==
  /\ m \in sent[s]
  /\ phase[d] = "gathering"
  /\ recvCount' = [recvCount EXCEPT ![d] = recvCount[d] + 1]
  /\ parent' = [parent EXCEPT ![d] = s]
  /\ sent' = [sent EXCEPT ![s] = sent[s] \ {m}]
  /\ UNCHANGED <<phase, answer>>

Answer(s, a) ==
  /\ phase[s] = "gathering"
  /\ answer' = [answer EXCEPT ![s] = a]
  /\ phase' = [phase EXCEPT ![s] = "done"]
  /\ UNCHANGED <<parent, sent, recvCount>>

Next ==
  \/ \E s \in Node : StartGather(s) \/ Answer(s, "yes") \/ Answer(s, "no")
  \/ \E m \in R, s, d \in Node : Send(m, s, d) \/ Receive(m, d, s)

InitSpec == Init

NextSpec == Next

Spec == InitSpec /\ [][NextSpec]_vars

AncestorProperties ==
  /\ \A n \in Node : (n # initiator) => parent[n] # NoNode
  /\ \A n \in Node : (n # initiator) => \E m \in R : m \in sent[parent[n]]
  /\ \A n \in Node : (n # initiator /\ parent[parent[n]] # NoNode) => parent[parent[n]] # n
  /\ \A n \in Node : (n # initiator /\ parent[parent[n]] # NoNode) => parent[parent[n]] # parent[n]
  /\ \A a, b \in Node : (a # NoNode /\ b # NoNode /\ parent[a] = b) => parent[b] # a

TestSpec == Init /\ [][Next]_vars

====
---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets
CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node /\ initiator \in Node

RECURSIVE RelSum(_, _)
RelSum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + RelSum(f, S \ {x})

N1 == Cardinality(Node)
I1 == initiator
R1 == R

VARIABLES parent, phase, answer, sent, acceptSet
vars == <<parent, phase, answer, sent, acceptSet>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ phase \in [Node -> {"init", "query", "ready", "done"}]
  /\ answer \in [Node -> BOOLEAN]
  /\ sent \in 0..RelSum(R, Node)
  /\ acceptSet \subseteq Node

Ancestor(n) == IF parent[n] = NoNode THEN {}
               ELSE {parent[n]} \cup Ancestor(parent[n])

AncestorProperties ==
  /\ \A n \in Node : n # initiator => initiator \in Ancestor(n)
  /\ \A m, n \in Node : m \in Ancestor(n) => n \notin Ancestor(m)

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ phase = [n \in Node |-> IF n = initiator THEN "ready" ELSE "init"]
  /\ answer = [n \in Node |-> TRUE]
  /\ sent = 0
  /\ acceptSet = {}

Query(n) ==
  /\ n # initiator
  /\ phase[n] = "init"
  /\ phase' = [phase EXCEPT ![n] = "query"]
  /\ sent' = sent + RelSum(R, {n})
  /\ UNCHANGED <<parent, answer, acceptSet>>

Answer(n) ==
  /\ phase[n] = "query"
  /\ \E r \in Node : r # n /\ answer[n]
  /\ answer' = [answer EXCEPT ![n] = TRUE]
  /\ acceptSet' = acceptSet \cup {n}
  /\ UNCHANGED <<parent, phase, sent>>

Refuse(n) ==
  /\ phase[n] = "query"
  /\ \E r \in Node : r # n /\ ~answer[n]
  /\ answer' = [answer EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<parent, phase, sent, acceptSet>>

Join(n) ==
  /\ phase[n] = "query"
  /\ answer[n]
  /\ \E r \in Node : r # n /\ answer[n]
  /\ parent' = [parent EXCEPT ![n] = CHOOSE r \in Node : r # n /\ answer[n]]
  /\ phase' = [phase EXCEPT ![n] = "ready"]
  /\ UNCHANGED <<answer, sent, acceptSet>>

Complete(n) ==
  /\ phase[n] = "ready"
  /\ \A m \in Node : parent[m] = n => phase[m] = "done"
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED <<parent, answer, sent, acceptSet>>

PrintGraph ==
  LET pairs == {<<n1, n2>> \in Node \X Node : n1 # n2}
  IN LET pairsStr == {n1 \in pairs : <<n1[1], " -- ", n1[2]>>}
     IN UNCHANGED <<parent, phase, answer, sent, acceptSet>>

Next ==
  \/ \E n \in Node : Query(n) \/ Answer(n) \/ Refuse(n) \/ Join(n) \/ Complete(n)
  \/ PrintGraph

Spec == Init /\ [][Next]_vars

TestSpec == Spec
====
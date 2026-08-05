---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS
  Node,
  initiator,
  R,
  NoNode

ASSUME NoNode \notin Node

VARIABLES parent, recv, passive, rphase

vars == <<parent, recv, passive, rphase>>

PrintRelation ==
  LET Rel == { <<n, m>> : n \in Node, m \in Node, n # m }
  IN
    PrintS(Rel)

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ recv \in [Node -> Node \cup {NoNode}]
  /\ passive \subseteq Node
  /\ rphase \in [Node -> 0..2]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ recv = [n \in Node |-> NoNode]
  /\ passive = {}
  /\ rphase = [n \in Node |-> IF n = initiator THEN 2 ELSE 0]

EchoStep ==
  LET mkt(n) ==
    /\ n \notin passive
    /\ \E m \in passive :
         /\ parent[n] = NoNode
         /\ recv[n] = m
         /\ parent' = [parent EXCEPT ![n] = m]
         /\ rphase' = [rphase EXCEPT ![n] = 2]
    /\ UNCHANGED <<recv, passive>>

  IN
    \/ \E m \in Node :
         /\ m \notin passive
         /\ parent[m] = NoNode
         /\ recv' = [recv EXCEPT ![initiator] = m]
         /\ UNCHANGED <<parent, passive, rphase>>
    \/ mkt(initiator)
    \/ \E m \in Node \ {initiator} : mkt(m)
    \/ \E n \in Node :
         /\ n \notin passive
         /\ rphase[n] = 2
         /\ \E m \in Node :
              /\ m \notin passive
              /\ m # n
              /\ parent[m] = NoNode
              /\ recv' = [recv EXCEPT ![n] = m]
              /\ UNCHANGED <<parent, passive, rphase>>
    \/ \E n \in Node :
         /\ n \notin passive
         /\ rphase[n] = 2
         /\ \E m \in Node :
              /\ parent[n] = m
              /\ active == {\k \in Node : rphase[k] = 2} \cup {initiator}
              /\ active # {}
              /\ LET alive == \E a \in active : recv[a] = n
                 IN \A a \in active : alive
              /\ parent' = [parent EXCEPT ![n] = NoNode]
              /\ passive' = passive \cup {n}
              /\ rphase' = [rphase EXCEPT ![n] = 0]
              /\ recv' = [recv EXCEPT ![n] = NoNode]

InitSpec == Init /\ PrintRelation

Spec == InitSpec /\ [][EchoStep]_vars

AncestorProperties ==
  /\ \A n \in Node \ {initiator} : parent[n] # NoNode
  /\ \A n \in Node : (parent[n] = NoNode) <=> (n = initiator)
  /\ \A n \in Node : (n # initiator /\ parent[n] # NoNode) => (parent[parent[n]] # n)

TestSpec == Spec

====
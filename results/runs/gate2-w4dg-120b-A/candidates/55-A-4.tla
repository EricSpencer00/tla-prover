---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

ASSUME initiator \in Node
ASSUME initiator # NoNode

VARIABLES echo, parent, acked, parentEcho
vars == <<echo, parent, acked, parentEcho>>

Init ==
  /\ echo = [n \in Node |-> IF n = initiator THEN 1 ELSE 0]
  /\ parent = [n \in Node |-> NoNode]
  /\ acked = [n \in Node |-> 0]
  /\ parentEcho = [n \in Node |-> 0]

SendEcho ==
  /\ \E src \in Node, dst \in Node :
       /\ src # dst
       /\ <<src, dst>> \in R
       /\ echo' = [echo EXCEPT ![dst] = 1]
       /\ parent' = [parent EXCEPT ![dst] = src]
  /\ UNCHANGED <<acked, parentEcho>>

SendAck ==
  /\ \E n \in Node :
       /\ echo[n] = 1
       /\ acked' = [acked EXCEPT ![n] = 1]
       /\ parentEcho' = [parentEcho EXCEPT ![n] = echo[parent[n]]]
  /\ UNCHANGED <<echo, parent>>

Reset ==
  /\ \A n \in Node : echo[n] = 1
  /\ \E n \in Node : acked[n] = 0
  /\ echo' = [n \in Node |-> IF acked[n] = 0 THEN 0 ELSE echo[n]]
  /\ parent' = [n \in Node |-> IF acked[n] = 0 THEN parent[n] ELSE parent[n]]
  /\ UNCHANGED <<acked, parentEcho>>

Initiate ==
  /\ echo[initiator] = 0
  /\ echo' = [echo EXCEPT ![initiator] = 1]
  /\ UNCHANGED <<parent, acked, parentEcho>>

Shutdown ==
  /\ \A n \in Node : echo[n] = 1
  /\ \A n \in Node : acked[n] = 1
  /\ echo' = echo
  /\ parent' = parent
  /\ acked' = acked
  /\ parentEcho' = parentEcho

Next == SendEcho \/ SendAck \/ Reset \/ Initiate \/ Shutdown

Spec == Spec == Init /\ [][Next]_vars

TestSpec == Spec /\ UNCHANGED vars /\ PrintR

PrintR == LET S == {<<src, dst>> \in R : src # dst} IN
             Print("\nFully meshed graph edges: " ^ ToString(S))

TypeOK ==
  /\ echo \in [Node -> 0..1]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ acked \in [Node -> 0..1]
  /\ parentEcho \in [Node -> 0..1]

AncestorProperties ==
  /\ (\A n \in Node : n # initiator => parent[n] # NoNode)
  /\ (\A n \in Node : n # initiator => parent[parent[n]] = NoNode)
====
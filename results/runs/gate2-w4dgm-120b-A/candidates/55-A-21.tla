---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

TypeOK ==
  /\ Node \subseteq STRING
  /\ initiator \in Node
  /\ R \subseteq (Node \X Node)
  /\ NoNode \notin Node

N1 == Node
I1 == initiator
R1 == R

Variables active, pending, done, saw, parent

vars == <<active, pending, done, saw, parent>>

NonePending == \A n \in Node : ~pending[n]

Init ==
  /\ active = TRUE
  /\ pending = [n \in Node |-> TRUE]
  /\ done = [n \in Node |-> FALSE]
  /\ saw = [n \in Node |-> {}]
  /\ parent = [n \in Node |-> NoNode]

Echo(n) ==
  /\ active
  /\ ~done[n]
  /\ pending[n]
  /\ \E m \in Node :
       /\ <<n, m>> \in R
       /\ m \notin saw[n]
       /\ saw' = [saw EXCEPT ![n] = saw[n] \cup {m}]
  /\ pending' = [pending EXCEPT ![n] = FALSE]
  /\ parent' = [parent EXCEPT ![n] = CHOOSE m \in Node : <<m, n>> \in R]
  /\ UNCHANGED <<active, done>>

DoneEcho(n) ==
  /\ active
  /\ ~done[n]
  /\ ~pending[n]
  /\ \A m \in Node : <<n, m>> \in R => done[m]
  /\ done' = [done EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<active, pending, saw, parent>>

Halt ==
  /\ active
  /\ \A n \in Node : done[n]
  /\ active' = FALSE
  /\ UNCHANGED <<pending, done, saw, parent>>

InitEcho == Init
NextEcho == Halt \/ (\E n \in Node : Echo(n) \/ DoneEcho(n))

Ancestor(m, n) == (m = n) \/ (parent[n] # NoNode /\ Ancestor(m, parent[n]))

AncestorProperties ==
  /\ \A n \in Node : active => ~pending[n]
  /\ \A n \in Node : parent[n] # NoNode => parent[n] \in Node
  /\ \A n \in Node : (active /\ done[n]) => Ancestor(initiator, n)
  /\ \A n \in Node : parent[n] # NoNode => ~Ancestor(n, parent[n])

TestSpec == InitEcho /\ [][NextEcho]_vars
====
---- MODULE MCEcho ----
EXTENDS Integers, TLC

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

N1 == Node
I1 == {initiator}
R1 == {R}

VARIABLES alive, parent, epoch, sentCount

vars == <<alive, parent, epoch, sentCount>>

State == [alive: BOOLEAN, parent: Node \cup {NoNode}, epoch: 0..3, sentCount: 0..3]

TypeOK ==
  /\ alive \in BOOLEAN
  /\ parent \in Node \cup {NoNode}
  /\ epoch \in 0..3
  /\ sentCount \in 0..3

Init ==
  /\ alive = FALSE
  /\ parent = NoNode
  /\ epoch = 0
  /\ sentCount = 0

InitEcho ==
  /\ \A n \in Node :
       n >= I1[1] =>
         /\ IF n = initiator THEN
              /\ alive' = TRUE
              /\ parent' = NoNode
              /\ epoch' = 1
              /\ sentCount' = 0
            ELSE
              /\ alive' = FALSE
              /\ parent' = NoNode
              /\ epoch' = 0
              /\ sentCount' = 0
  /\ UNCHANGED <<alive, parent, epoch, sentCount>>

ExploreEcho ==
  /\ epoch < 3
  /\ epoch' = epoch + 1
  /\ sentCount' = (sentCount + 1) % 4
  /\ UNCHANGED <<alive, parent>>

NextEcho == InitEcho \/ ExploreEcho

SpecEcho == Init /\ [][NextEcho]_vars

AncestorProperties ==
  /\ (alive => (parent = NoNode \/ parent \in Node))
  /\ (parent # NoNode => ~ (parent \in {n \in Node : alive /\ parent = n}))
  /\ (parent = NoNode => alive)

TestSpec == SpecEcho

====
---- MODULE MCReachable ----
EXTENDS ReachSeq, Sequences

CONSTANTS Nodes, Root, Succ, Seq

CONSTANT
  Nodes = {1, 2, 3, 4}
  Root  = 1
  Succ  = [i \in Nodes |
           IF i = 1 THEN {2, 3}
           ELSE IF i = 2 THEN {1, 4}
           ELSE IF i = 3 THEN {2, 4}
           ELSE {1, 3}]
  Seq   = {s \in ^{Nodes} : Len(s) <= Len(Nodes)}

Variables == {marked, frontier, pc}

Spec == Init /\ [][Next]_Variables

TypeOK          == ReachSeqTypeOK
Inv1            == ReachSeqInv1
Inv2            == ReachSeqInv2
Inv3            == ReachSeqInv3
PartialCorrectness == ReachSeqPartialCorrectness

Termination == ReachSeqTermination
====
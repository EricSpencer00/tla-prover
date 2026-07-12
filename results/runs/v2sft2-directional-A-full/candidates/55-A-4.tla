---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, Print, Echo

CONSTANTS Node, initiator, R, NoNode

CONSTANTS Node = {"node1", "node2", "node3"},
          initiator = "node1",
          R = { <<n, m>> \in Node \XNode : n # m },
          NoNode = "NoParent"

Init          == Echo.Init
Next          == Echo.Next

PrintAdjacency == Print("Adjacency relation R: ", R) /\ UNCHANGED <<>>

InitWithPrint == Init /\ PrintAdjacency

TestSpec == InitWithPrint /\ [][Next]

TypeOK          == Echo.TypeOK
AncestorProperties == Echo.AncestorProperties

====
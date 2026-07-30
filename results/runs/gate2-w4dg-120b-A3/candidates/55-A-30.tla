---- MODULE MCEcho ----
EXTENDS Naturals, TLC

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

TypeOK ==
    /\ Node \subseteq STRING
    /\ initiator \in STRING
    /\ initiator \in Node
    /\ R \subseteq [a: STRING, b: STRING]
    /\ NoNode \notin Node

Nodes == {"n1", "n2", "n3"}

INIT ==
    /\ Node = Nodes
    /\ initiator = CHOOSE n \in Node : TRUE
    /\ R = {p \in [a: STRING, b: STRING] :
                (p.a # p.b) /\ (p.a \in Nodes /\ p.b \in Nodes)}
    /\ TRUE

SpecInit == INIT

\* The Echo algorithm's actions: the full set is inherited from the Echo spec.
InitAction == SpecInit

Next == InitAction

Spec == SpecInit /\ [][Next]_<<Node, initiator, R>>

\* A test-only variant that prints the adjacency relation as a side effect.
PrintGraph ==
    /\ UNCHANGED <<Node, initiator, R>>
    /\ Print("Adjacency relation: " ^ STRING(R))

AncestorProperties ==
    /\ \A n \in Node : initiator # n => initiator \in Ancestors(n)
    /\ \A x, y \in Node : (x \in Ancestors(y)) => (~(y \in Ancestors(x)))

SpecPrintGraph ==
    /\ Spec
    /\ PrintGraph

====
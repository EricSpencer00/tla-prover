---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

CONSTANTS N1, I1, R1

\* The test variant is purely for visibility: it prints the graph adjacency at
\* runtime so a human can see which fully-meshed graph is instantiated.
PrintAdjacency == Print("Adjacency relation for this model: " \o ToString(R))

TypeOK ==
    /\ Node \subseteq { "n1", "n2", "n3" }
    /\ initiator \in Node
    /\ \A x \in Node : NoNode \notin Node \cup { x }
    /\ R \subseteq Node \X Node
    /\ \A a \in Node : << a, a >> \notin R
    /\ \A a, b \in Node : (<< a, b >> \in R) => (<< b, a >> \in R)

\* EchoStub: the Echo specification's state is entirely left untouched here.
Init == PrintAdjacency
Next == Init
Spec == Init /\ [][Next]_<< >>
AncestorProperties == TRUE

\* The .cfg overrides Node/initiator/R with the bounded versions N1/I1/R1,
\* but the specification must be type-correct even for those bounded versions.
TypeOKBound ==
    /\ N1 \subseteq Node
    /\ I1 \subseteq { initiator }
    /\ R1 \subseteq R

TestSpec == Spec

====
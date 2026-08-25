---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* Concrete instantiation of the abstract constants for model checking *)

N1 == {"n1", "n2", "n3"}                \* the set of three nodes
I1 == "n1"                               \* the deterministic initiator
NoNode == "NoNode"                       \* sentinel value distinct from all nodes
R1 == { << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >> }  \* fully‑meshed, symmetric, irreflexive relation

(* Optional startup action that prints the adjacency relation; useful for debugging *)
InitPrint ==
    /\ Print("Adjacency relation R: " \o ToString(R))
    /\ TRUE

(* The initial predicate combines the original Echo initialization with the optional print *)
TestInit == Echo!Init /\ InitPrint

(* The next-state relation is the one defined in Echo *)
TestNext == Echo!Next

(* Full specification used by the .cfg file *)
TestSpec == TestInit /\ [][TestNext]_(Echo!vars)

=============================================================================
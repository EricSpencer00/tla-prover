---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Node, initiator, R, NoNode,
    inbox, children, nbrs, rcvd, parent, pc

\* Concrete three‑node fully‑connected graph
N1 == {"n1", "n2", "n3"}

\* Deterministically chosen initiator
I1 == "n1"

\* Undirected, irreflexive adjacency relation (fully meshed)
R1 == (N1 \X N1) \ { <<n,n>> : n \in N1 }

\* Sentinel value for “no parent”, distinct from all nodes
ASSUME NoNode \notin N1

\* Concrete definitions for the remaining constants required by Echo
inbox  == [n \in N1 |-> {}]                                         \* empty message buffers
children == [n \in N1 |-> {}]                                       \* no children initially
nbrs   == [n \in N1 |-> { m \in N1 : <<n,m>> \in R1 }]              \* neighbor set derived from R1
rcvd   == [n \in N1 |-> FALSE]                                      \* no node has received a message yet
parent == [n \in N1 |-> NoNode]                                     \* no parent assigned initially
pc     == [n \in N1 |-> "init"]                                     \* initial program counter value

\* Instantiate the generic Echo specification with the concrete constants
INSTANCE Echo WITH
    Node       <- N1,
    initiator  <- I1,
    R          <- R1,
    NoNode     <- NoNode,
    inbox      <- inbox,
    children   <- children,
    nbrs       <- nbrs,
    rcvd       <- rcvd,
    parent     <- parent,
    pc         <- pc

\* The specification to be checked
TestSpec == Echo!Spec

\* Safety invariants inherited from Echo
TypeOK == Echo!TypeOK
AncestorProperties == Echo!AncestorProperties
====
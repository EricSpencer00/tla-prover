---- MODULE MCEcho ----
EXTENDS FiniteSets, Sequences, TLC

CONSTANTS Node, initiator, R, NoNode

\* ----------------------------------------------------------------------
\* The graph is a fully-meshed undirected graph over Node.  R is the
\* adjacency relation.  It is irreflexive, symmetric, and connects every
\* distinct pair of nodes.
\* ----------------------------------------------------------------------
R == { <<x,y>> \in Node \X Node | x \in Node /\ y \in Node /\ x # y }

\* ----------------------------------------------------------------------
\* Variables inherited from the base Echo specification
\* ----------------------------------------------------------------------
VARIABLES P, A, S, Msg

\* ----------------------------------------------------------------------
\* Type correctness assumption (required by the invariants)
\* ----------------------------------------------------------------------
TypeOK == 
    /\ P \in [Node -> Node \cup {NoNode}]
    /\ A \in [Node -> Node \cup {NoNode}]
    /\ S \in [Node -> BOOLEAN]
    /\ Msg \in [Node -> [Node -> BOOLEAN]]

\* ----------------------------------------------------------------------
\* Initial state: only the initiator has sent a message; all others are
\* waiting.  The initiator's parent is NoNode.  The spanning tree relation
\* is empty initially.
\* ----------------------------------------------------------------------
Init ==
    /\ P = [n \in Node |-> NoNode]
    /\ A = [n \in Node |-> NoNode]
    /\ S = [n \in Node |-> FALSE]
    /\ Msg = [n \in Node |-> [m \in Node |-> FALSE]]
    /\ S[initiator] = TRUE
    /\ Msg = [n \in Node |-> [m \in Node |-> FALSE]]

\* ----------------------------------------------------------------------
\* Actions as defined in the base Echo specification
\* ----------------------------------------------------------------------
Send == \E n \in Node :
    /\ n \in Node
    /\ ~S[n]
    /\ \E p \in Node : p \in Node /\ p # n /\ p \in Node
    /\ S' = [S EXCEPT ![n] = TRUE]
    /\ Msg' = [Msg EXCEPT ![n] = [Msg[n] EXCEPT ![p] = TRUE]]
    /\ UNCHANGED <<P, A>>

Receive == \E n \in Node, p \in Node :
    /\ n \in Node /\ p \in Node
    /\ Msg[n][p]
    /\ Msg' = [Msg EXCEPT ![n] = [Msg[n] EXCEPT ![p] = FALSE]]
    /\ P' = [P EXCEPT ![n] = p]
    /\ A' = [A EXCEPT ![n] = p]
    /\ UNCHANGED <<S, Msg>>

\* ----------------------------------------------------------------------
\* Definition of the next-state relation
\* ----------------------------------------------------------------------
Next == Send \/ Receive

\* ----------------------------------------------------------------------
\* The base specification for the Echo algorithm
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<P, A, S, Msg>>

\* ----------------------------------------------------------------------
\* Test variant that prints the graph adjacency relation at startup
\* ----------------------------------------------------------------------
TestSpec == 
    Init /\ 
    \E dummy \in Node : 
        Print("Graph adjacency R =", R); 
        UNCHANGED <<P, A, S, Msg>>

\* ----------------------------------------------------------------------
\* Ancestor relation (the directed spanning tree)
\* ----------------------------------------------------------------------
Ancestors == \lambda n, m \in Node : 
    IF n = m THEN FALSE
    ELSE IF A[n] = m THEN TRUE
    ELSE A[n] \in Node /\ Ancestors[A[n], m]

\* ----------------------------------------------------------------------
\* Ancestor property: the initiator is an ancestor of every other node
\* and there are no cycles (the ancestor relation is transitive and irreflexive).
\* ----------------------------------------------------------------------
AncestorProperties == 
    /\ \A n \in Node : 
          n = initiator \/ Ancestors[n, initiator]
    /\ \A n, m, k \in Node :
          Ancestors[n, m] /\ Ancestors[m, k] => Ancestors[n, k]
    /\ \A n \in Node : ~Ancestors[n, n]

\* ----------------------------------------------------------------------
\* Specification operator for TLC
\* ----------------------------------------------------------------------
Spec == TestSpec

\* ----------------------------------------------------------------------
\* The specification must include the type correctness invariant.
\* ----------------------------------------------------------------------
Init == Init
Next == Next
TypeOK == TypeOK
AncestorProperties == AncestorProperties

====
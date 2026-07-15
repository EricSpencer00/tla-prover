---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----- Constants required by the .cfg -----
CONSTANT Node, initiator, R, NoNode

\* ----- Derived collections -----
NodeSet == Node

\* ----- State variables (same as in Echo) -----
VARIABLES parent, sent, recv

\* ----- Type definitions for readability -----
Parent == [n \in NodeSet |-> (NoNode \cup NodeSet)]
SentSet == [n \in NodeSet |-> SUBSET NodeSet]
RecvSet == [n \in NodeSet |-> SUBSET NodeSet]

\* ----- Initial state (inherits Echo's INIT) -----
Init ==
    /\ parent = [n \in NodeSet |-> NoNode]
    /\ sent   = [n \in NodeSet |-> {}]
    /\ recv   = [n \in NodeSet |-> {}]
    /\ initiator \in NodeSet
    /\ NoNode \notin NodeSet

\* ----- Actions (inherit Echo's actions) -----
Send ==
    \E i \in NodeSet, j \in NodeSet :
        /\ i # j
        /\ (i,j) \in R
        /\ j \notin sent[i]
        /\ sent' = [sent EXCEPT ![i] = sent[i] \cup {j}]
        /\ UNCHANGED <<parent, recv>>

Recv ==
    \E i \in NodeSet, j \in NodeSet :
        /\ i # j
        /\ (j,i) \in R
        /\ j \in sent[i]
        /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {j},
                              ![j] = recv[j] \cup {i}]
        /\ UNCHANGED <<parent, sent>>

SetParent ==
    \E i \in NodeSet, p \in NodeSet :
        /\ i # p
        /\ (p,i) \in R
        /\ parent[i] = NoNode
        /\ parent' = [parent EXCEPT ![i] = p]
        /\ UNCHANGED <<sent, recv>>

\* The overall next-state relation includes all actions.
Next == \/ Send
        \/ Recv
        \/ SetParent

\* ----- Specification -----
Spec == Init /\ [][Next]_<<parent, sent, recv>>

\* ----- Safety invariants -----
TypeOK ==
    /\ parent \in Parent
    /\ sent   \in SentSet
    /\ recv   \in RecvSet
    /\ \A i \in NodeSet : sent[i] \subseteq NodeSet
    /\ \A i \in NodeSet : recv[i] \subseteq NodeSet

Ancestor(i, j) == 
    (i = j) \/ (\E p \in NodeSet : parent[j] = p /\ Ancestor(i, p))

AncestorProperties ==
    /\ \A n \in NodeSet : n # initiator => initiator \in Ancestor(initiator, n)
    /\ \A i, j \in NodeSet : i # j => i \notin Ancestor(j, i)

\* ----- TestSpec prints the graph adjacency at startup -----
TestSpec ==
    /\ Spec
    /\ \E _ \in {1} :
        /\ PrintAdjacency()

PrintAdjacency() ==
    /\ Print("Adjacency relation R:")
    /\ Print(R)

\* ----- The configuration expects these names -----
Termination == []_(<<parent, sent, recv>>)_Spec

\* The specification name for the .cfg
TestSpecSpec == TestSpec

\* The invariants referenced by the .cfg
Inv1 == TypeOK
Inv2 == AncestorProperties

\* Provide the identifiers with the exact names required
Spec == TestSpec
TypeOK == Inv1
AncestorProperties == Inv2

====
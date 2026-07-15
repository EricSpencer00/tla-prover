---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Node,        \* The set of node identifiers (e.g., {"a","b","c"})
    initiator,   \* The distinguished initiator node
    R,           \* Undirected adjacency relation (symmetric, irreflexive)
    NoNode       \* Sentinel value meaning “no parent”

(* --------------------------------------------------------------------- *)
(* Derived constants required by the Echo algorithm                     *)
(* --------------------------------------------------------------------- *)

(* The set of all possible directed edges (parent relationships)      *)
Parents == Node \cup {NoNode}

(* --------------------------------------------------------------------- *)
(* Variables                                                            *)
(* --------------------------------------------------------------------- *)

VARIABLES
    parent,          \* parent[n] gives the parent of node n (or NoNode)
    sent,            \* sent[n] = TRUE iff n has already sent its echo
    initiated        \* initiated = TRUE after the initiator starts

(* --------------------------------------------------------------------- *)
(* Type correctness invariant                                            *)
(* --------------------------------------------------------------------- *)

TypeOK ==
    /\ parent \in [Node -> Parents]
    /\ sent   \in [Node -> BOOLEAN]
    /\ initiated \in BOOLEAN

(* --------------------------------------------------------------------- *)
(* Initial predicate                                                     *)
(* --------------------------------------------------------------------- *)

Init ==
    /\ parent   = [n \in Node |-> NoNode]
    /\ sent     = [n \in Node |-> FALSE]
    /\ initiated = FALSE

(* --------------------------------------------------------------------- *)
(* Actions                                                               *)
(* --------------------------------------------------------------------- *)

(* The initiator starts the algorithm *)
Initiate ==
    /\ ~initiated
    /\ initiated' = TRUE
    /\ UNCHANGED << parent, sent >>

(* A node n sends an echo message to its parent (if it has one)       *)
SendEcho ==
    \E n \in Node :
        /\ initiated
        /\ ~sent[n]
        /\ sent' = [sent EXCEPT ![n] = TRUE]
        /\ UNCHANGED << parent, initiated >>

(* A node n selects a parent from its neighbors (excluding NoNode)     *)
ChooseParent ==
    \E n \in Node :
        /\ ~initiated
        /\ sent[n] = FALSE
        /\ \E p \in Node :
               /\ p # n
               /\ <<n,p>> \in R
               /\ parent' = [parent EXCEPT ![n] = p]
        /\ UNCHANGED << sent, initiated >>

Next ==
    \/ Initiate
    \/ ChooseParent
    \/ SendEcho

(* --------------------------------------------------------------------- *)
(* Specification                                                         *)
(* --------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<parent, sent, initiated>>

(* The name required by the .cfg file                                    *)
TestSpec == Spec

(* --------------------------------------------------------------------- *)
(* Safety invariant: ancestor properties (acyclic and initiator root)  *)
(* --------------------------------------------------------------------- *)

\* Helper: computes the ancestor chain of node n
AncestorChain(n) ==
    IF parent[n] = NoNode THEN {}
    ELSE {parent[n]} \cup AncestorChain(parent[n])

AncestorProperties ==
    /\ initiator \in Node
    /\ \A n \in Node :
          (n # initiator) => (initiator \in AncestorChain(n))
    /\ \A n \in Node :
          ~ (n \in AncestorChain(n))   \* acyclicity

(* --------------------------------------------------------------------- *)
(* Theorem (optional, for readability)                                   *)
(* --------------------------------------------------------------------- *)

THEOREM Spec => []TypeOK

=============================================================================
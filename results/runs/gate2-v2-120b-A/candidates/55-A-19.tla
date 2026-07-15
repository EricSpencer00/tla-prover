---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(*  Constants required by the reference .cfg                               *)
(***************************************************************************)
CONSTANTS
    Node,          \* the set of node identifiers (to be bound by the .cfg)
    initiator,     \* the distinguished initiator node
    R,             \* the adjacency relation (a set of unordered pairs)
    NoNode         \* a distinguished value meaning "no parent"

(***************************************************************************)
(*  Derived constant: the set of unordered node pairs (edges)               *)
(***************************************************************************)
UndirectedEdge == { <<i, j>> : i \in Node, j \in Node, i # j }

\* The configuration file must bind R to a subset of UndirectedEdge that
\* is symmetric, irreflexive and (together with Node) connected.
\* For the fully‑meshed graph used in the exhaustive model, R would be
\* exactly UndirectedEdge.

(***************************************************************************)
(*  State variables (same as in the Echo specification)                    *)
(***************************************************************************)
VARIABLES
    parent,        \* [n \in Node |-> NoNode] means node n has no parent yet
    sent,          \* [n \in Node |-> FALSE] indicates whether n has sent its messages
    done           \* [n \in Node |-> FALSE] indicates whether n has completed its role

(***************************************************************************)
(*  Helper definitions                                                    *)
(***************************************************************************)
Neighbors(n) == { m \in Node : <<n, m>> \in R \/ <<m, n>> \in R }

Ancestor(n, p) ==
    /\ p \in Node
    /\ RECURSIVE Ancestor(_,_)
    /\ (p = initiator) \/ (p \in Node /\ parent[p] # NoNode /\ Ancestor(parent[p], p))

(* The above definition is not used directly but appears in the invariant. *)

(***************************************************************************)
(*  Initial state (INIT)                                                  *)
(***************************************************************************)
Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ sent   = [n \in Node |-> FALSE]
    /\ done   = [n \in Node |-> FALSE]
    /\ sent[initiator] = TRUE
    /\ parent[initiator] = initiator   \* initiator points to itself (a common convention)

(***************************************************************************)
(*  Actions (NEXT) – a faithful copy of the Echo algorithm actions          *)
(***************************************************************************)
SendMsg ==
    \E i \in Node :
        /\ sent[i] = FALSE
        /\ sent' = [sent EXCEPT ![i] = TRUE]
        /\ UNCHANGED <<parent, done>>

ReceiveMsg ==
    \E i \in Node :
        /\ sent[i] = TRUE
        /\ \E j \in Neighbors(i) :
            /\ parent[i] = NoNode
            /\ parent' = [parent EXCEPT ![i] = j]
            /\ sent'   = [sent EXCEPT ![i] = FALSE]
            /\ UNCHANGED done

Finish ==
    \E i \in Node :
        /\ sent[i] = FALSE
        /\ done[i] = FALSE
        /\ parent[i] # NoNode
        /\ done' = [done EXCEPT ![i] = TRUE]
        /\ UNCHANGED <<parent, sent>>

Next ==
    \/ SendMsg
    \/ ReceiveMsg
    \/ Finish
    \/ UNCHANGED <<parent, sent, done>>

(***************************************************************************)
(*  Specification formula (TestSpec)                                      *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<parent, sent, done>>

(***************************************************************************)
(*  Safety properties (invariants)                                        *)
(***************************************************************************)
TypeOK ==
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ sent   \in [Node -> BOOLEAN]
    /\ done   \in [Node -> BOOLEAN]
    /\ \A n \in Node :
        IF parent[n] = NoNode THEN TRUE
        ELSE parent[n] \in Node

AncestorProperties ==
    /\ initiator \in Node
    /\ \A n \in Node :
        IF n = initiator THEN TRUE
        ELSE
            /\ parent[n] # NoNode
            /\ \E p \in Node : Ancestor(n, p)
    /\ \A n \in Node :
        parent[n] # n          \* No node points to itself (except initiator, handled above)

(***************************************************************************)
(*  Export the symbols required by the .cfg file                             *)
(***************************************************************************)
THEOREM Spec => []TypeOK
THEOREM Spec => []AncestorProperties

(*
  The .cfg file is expected to contain:
    CONSTANTS Node = {"A", "B", "C"}
    initiator = "A"
    R = { << "A", "B" >>, << "A", "C" >>, << "B", "C" >> }
    NoNode = "None"
    SPECIFICATION TestSpec
    INVARIANT TypeOK
    INVARIANT AncestorProperties
*)

=============================================================================
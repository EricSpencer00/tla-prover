---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants (to be bound by the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS Node, initiator, R, NoNode

(*--------------------------------------------------------------------
  Derived constants for readability
--------------------------------------------------------------------*)
VARIABLES parent, children, visited, sent

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)

(* Parent of a node, NoNode means no parent assigned yet *)
Parent == parent

(* Children set of a node *)
Children == children

(* Whether a node has already sent its echo message *)
Sent == sent

(* The set of all nodes *)
Nodes == Node

(* The initiator node *)
Initiator == initiator

(* The graph adjacency relation (given by constant R) *)
Adj == R

(*--------------------------------------------------------------------
  Type correctness invariant (part of the required invariants)
--------------------------------------------------------------------*)
TypeOK ==
    /\ parent \in [Nodes -> (Nodes \cup {NoNode})]
    /\ children \in [Nodes -> SUBSET Nodes]
    /\ visited \in SUBSET Nodes
    /\ sent \in SUBSET Nodes
    /\ initiator \in Nodes
    /\ NoNode \notin Nodes
    /\ initiator \notin visited

(*--------------------------------------------------------------------
  Safety property: Ancestor (spanning tree) properties
--------------------------------------------------------------------*)
AncestorProperties ==
    /\ \A n \in Nodes \ {Initiator} :
          parent[n] # NoNode
    /\ \A n \in Nodes :
          (parent[n] = NoNode) => (n = Initiator)
    /\ \A n \in Nodes :
          ~ (n \in visited) => (parent[n] = NoNode)
    /\ \A n \in Nodes :
          (parent[n] # NoNode) => (parent[n] \in Nodes)
    /\ \A n \in Nodes :
          (parent[n] # NoNode) =>
            (parent[n] \in Adj[n])
    /\ \A n \in Nodes :
          (NoNode \notin children[n])
    /\ \A n \in Nodes :
          (children[n] = {}) => (n = Initiator)
    /\ \A n \in Nodes :
          n \in visited => (parent[n] = NoNode \/ parent[n] \in visited)

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ parent = [n \in Nodes |-> NoNode]
    /\ children = [n \in Nodes |-> {}]
    /\ visited = {}
    /\ sent = {}

(*--------------------------------------------------------------------
  Action definitions
--------------------------------------------------------------------*)

(* Initiator sends its message to all neighbors *)
InitiatorSend ==
    /\ parent[Initiator] = NoNode
    /\ sent' = visited
    /\ visited' = visited \cup {Initiator}
    /\ UNCHANGED <<parent, children>>

(* A non-initiator node that has not yet been visited receives a message
   from a neighbor and records that neighbor as its parent. *)
Receive ==
    \E n \in Nodes \ {Initiator} :
        /\ parent[n] = NoNode
        /\ \E nbr \in Adj[n] :
              /\ nbr \in visited
              /\ parent' = [parent EXCEPT ![n] = nbr]
              /\ visited' = visited \cup {n}
              /\ UNCHANGED <<children, sent>>

(* A node that has already recorded a parent and has not yet sent its echo
   sends the echo to its parent. *)
EchoSend ==
    \E n \in Nodes :
        /\ n # Initiator
        /\ parent[n] # NoNode
        /\ n \notin sent
        /\ sent' = sent \cup {n}
        /\ children' = [children EXCEPT ![parent[n]] = @ \cup {n}]
        /\ UNCHANGED <<parent, visited>>

(* The initiator may decide to terminate after it has received echoes
   from all its children. *)
Terminate ==
    /\ Initiator \in visited
    /\ \A n \in Nodes : n # Initiator => n \in sent
    /\ UNCHANGED <<parent, children, visited, sent>>

Next ==
    \/ InitiatorSend
    \/ Receive
    \/ EchoSend
    \/ Terminate

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<parent, children, visited, sent>>

(*--------------------------------------------------------------------
  Names required by the .cfg file
--------------------------------------------------------------------*)
TestSpec == Spec
vars == <<parent, children, visited, sent>>
InitState == Init
NextState == Next
TypeOKInv == TypeOK
AncestorInv == AncestorProperties

====
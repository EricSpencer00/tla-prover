---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, children, status, msgQueue, active, ancestors

(* --algorithm Echo (informal description) omitted, we directly specify the actions *)

(* Type definitions *)
Parent == [Node -> (Node \cup {NoNode})]
Children == [Node -> SUBSET Node]
Status == [Node -> {"idle", "pending"}]
MsgQueue == [Node -> Seq(Node)]
Ancestors == [Node -> SUBSET Node]

(* Initial state *)
Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ children = [n \in Node |-> {}]
    /\ status = [n \in Node |-> "idle"]
    /\ msgQueue = [n \in Node |-> <<>>]
    /\ active = {initiator}
    /\ ancestors = [n \in Node |-> {}]

(* Helper definitions *)
IsLeaf(n) == /\ n \notin initiator
               /\ \A m \in Node: m # n => m \notin parent[n]

Send(n, m) ==
    /\ msgQueue' = [msgQueue EXCEPT ![m] = Append(@, n)]
    /\ UNCHANGED <<parent, children, status, active, ancestors>>

Receive(n) ==
    /\ \E sender \in Node:
          /\ Len(msgQueue[n]) > 0
          /\ sender = Head(msgQueue[n])
          /\ msgQueue' = [msgQueue EXCEPT ![n] = Tail(@)]
          /\ parent' = [parent EXCEPT ![n] = sender]
          /\ status' = [status EXCEPT ![n] = "pending"]
          /\ active' = active \cup {n}
    /\ UNCHANGED <<children, msgQueue, ancestors>>

Acknowledge(n) ==
    /\ n \in active
    /\ \E child \in Node:
          /\ child # n
          /\ parent[child] = n
          /\ status[child] = "idle"
          /\ status' = [status EXCEPT ![child] = "pending"]
    /\ UNCHANGED <<parent, children, msgQueue, active, ancestors>>

Terminate ==
    /\ \A n \in Node: n # initiator => parent[n] # NoNode
    /\ ancestors = [n \in Node |-> 
          IF n = initiator THEN {}
          ELSE {parent[n]} \cup ancestors[parent[n]]]
    /\ UNCHANGED <<parent, children, status, msgQueue, active>>

Next ==
    \/ \E n \in Node: Receive(n)
    \/ \E n \in Node: Acknowledge(n)
    \/ Terminate

(* Safety invariants *)
TypeOK ==
    /\ parent \in Parent
    /\ children \in Children
    /\ status \in Status
    /\ msgQueue \in MsgQueue
    /\ active \subseteq Node
    /\ ancestors \in Ancestors

AncestorProperties ==
    /\ \A n \in Node: initiator \in ancestors[n] \/ n = initiator
    /\ \A n \in Node: initiator \notin {n}
    /\ \A n \in Node: NoNode \notin ancestors[n]
    /\ \A n \in Node: n \notin ancestors[n]   \* acyclicity

(* Specification and properties as required by the cfg *)
Spec == Init /\ [][Next]_<<parent, children, status, msgQueue, active, ancestors>>
TestSpec == Spec
TypeOKInv == TypeOK
AncestorPropInv == AncestorProperties

=============================================================================
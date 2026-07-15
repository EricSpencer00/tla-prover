---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Node, initiator, R, NoNode

(*-----------------------------------------------------------------
  Derived from the Echo algorithm specification.  The Echo spec
  defines the following elements which we reproduce here adapted
  to the constants above.
-----------------------------------------------------------------*)

VARIABLES parent, received

(* alias for readability *)
vars == << parent, received >>

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
NodeSet == Node
ParentSet == NodeSet \cup {NoNode}
ReceivedSet == SUBSET NodeSet

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ parent = [n \in NodeSet |-> NoNode]
    /\ received = {}

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Neighbors(n) == { m \in NodeSet : <<n, m>> \in R }

CanSend(n) == /\ parent[n] = NoNode
            /\ n # initiator
            /\ \E m \in Neighbors(n) : parent[m] = NoNode

SendAction ==
    \E n \in NodeSet :
        /\ CanSend(n)
        /\ \E m \in Neighbors(n) :
            /\ parent' = [parent EXCEPT ![m] = n]
            /\ received' = received \cup {n}
            /\ UNCHANGED << >>

Terminate ==
    /\ \A n \in NodeSet : parent[n] # NoNode \/ n = initiator
    /\ UNCHANGED << parent, received >>

Next == SendAction \/ Terminate

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
TestSpec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)

(* Type correctness *)
TypeOK ==
    /\ parent \in [NodeSet -> ParentSet]
    /\ received \in ReceivedSet

(* Ancestor relation: no cycles and initiator is ancestor of all *)
Ancestor == { <<n, m>> \in NodeSet \X NodeSet : parent[m] = n }

Acyclic ==
    \A n \in NodeSet : ~(<<n, n>> \in (Ancestor)^+)

AllReachable ==
    \A n \in NodeSet \ {initiator} :
        \E p \in NodeSet :
            <<initiator, p>> \in (Ancestor)^*

AncestorProperties == Acyclic /\ AllReachable

=============================================================================
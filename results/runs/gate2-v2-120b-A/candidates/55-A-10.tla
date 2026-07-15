---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants required by the reference configuration
--------------------------------------------------------------------*)
CONSTANTS Node, initiator, R, NoNode

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Children == Node \ {initiator}

(*--------------------------------------------------------------------
  Variables (as in the Echo specification)
--------------------------------------------------------------------*)
VARIABLES parent, sent

(*--------------------------------------------------------------------
  Type predicates
--------------------------------------------------------------------*)
ParentType(p) == p = NoNode \/ p \in Node
SentType(s)   == s \in [Node -> BOOLEAN]

(*--------------------------------------------------------------------
  Initial state (inherits Echo's INIT, instantiated for the three-node
  fully‑meshed graph).  All nodes start with no parent and have not yet
  sent a message.
--------------------------------------------------------------------*)
Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ sent   = [n \in Node |-> FALSE]

(*--------------------------------------------------------------------
  Actions (as in Echo).  For readability we keep the same names.
--------------------------------------------------------------------*)
Send(u) ==
    /\ u \in Node
    /\ ~sent[u]
    /\ sent' = [sent EXCEPT ![u] = TRUE]
    /\ UNCHANGED parent

Receive(v, u) ==
    /\ v \in Node
    /\ u \in Node
    /\ u # v
    /\ sent[u]               \* u has already sent
    /\ ~sent[v]              \* v has not yet sent
    /\ parent' = [parent EXCEPT ![v] = u]
    /\ sent'   = [sent   EXCEPT ![v] = TRUE]
    /\ UNCHANGED <<>>

Terminate ==
    /\ \A n \in Node: sent[n]
    /\ UNCHANGED <<parent, sent>>

Next ==
    \/ \E u \in Node: Send(u)
    \/ \E v \in Node: \E u \in Node: Receive(v, u)
    \/ Terminate

(*--------------------------------------------------------------------
  Specification required by the .cfg file
--------------------------------------------------------------------*)
TestSpec == Init /\ [][Next]_<<parent, sent>>

(*--------------------------------------------------------------------
  Safety invariants required by the .cfg file
--------------------------------------------------------------------*)
TypeOK ==
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ sent   \in [Node -> BOOLEAN]

AncestorRel ==
    { <<p, c>> : c \in Node /\ parent[c] = p }

AcyclicAncestors ==
    /\ NoNode \notin Node
    /\ \A n \in Node: n \notin Domain(parent)
    /\ \A n \in Node: 
        \A p \in Node: 
            (<<n, p>> \in ^AncestorRel) => n # p

InitiatorIsRoot ==
    /\ parent[initiator] = NoNode

AllReachInitiator ==
    \A n \in Node: 
        (n = initiator) \/ 
        \E p \in Node: (<<p, n>> \in ^AncestorRel) /\ p = initiator

AncestorProperties == 
    /\ InitiatorIsRoot
    /\ AllReachInitiator
    /\ AcyclicAncestors

(*--------------------------------------------------------------------
  The .cfg file also expects the SPECIFICATION operator named "TestSpec"
  and the invariants named "TypeOK" and "AncestorProperties".
--------------------------------------------------------------------*)

====
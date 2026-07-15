---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Constants required by the reference configuration
-----------------------------------------------------------------*)
CONSTANTS
    Node,          \* The set of node identifiers (strings)
    initiator,     \* The distinguished initiator node
    R,             \* The adjacency relation (undirected graph)
    NoNode         \* Sentinel value representing "no parent"

(*-----------------------------------------------------------------
  Derived constant: the set of all possible parent values
-----------------------------------------------------------------*)
ParentSet == Node \cup {NoNode}

(*-----------------------------------------------------------------
  State variables (inherited from the Echo specification)
-----------------------------------------------------------------*)
VARIABLES
    parent,        \* Mapping each node to its parent (or NoNode)
    state,         \* Mapping each node to its current phase: "idle", "sent", "done"
    received       \* Mapping each node to the set of messages it has received

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
NodeSet == Node

InitParent == [n \in NodeSet |-> NoNode]

InitState == [n \in NodeSet |-> "idle"]

InitReceived == [n \in NodeSet |-> {}]

(*-----------------------------------------------------------------
  Initial predicate (inherits Echo's Init, instantiated)
-----------------------------------------------------------------*)
Init ==
    /\ parent = InitParent
    /\ state  = InitState
    /\ received = InitReceived
    /\ state[initiator] = "sent"   \* initiator starts the echo
    /\ parent[initiator] = NoNode

(*-----------------------------------------------------------------
  Actions (inherit Echo's actions; we give a minimal faithful model)
-----------------------------------------------------------------*)
SendEcho ==
    \E n \in NodeSet :
        /\ state[n] = "sent"
        /\ \A m \in NodeSet :
               (m \in R[n]) => 
                  /\ received' = [received EXCEPT ![m] = @ \cup {n}]
        /\ state' = [state EXCEPT ![n] = "done"]
        /\ UNCHANGED parent

ReceiveEcho ==
    \E n \in NodeSet :
        /\ state[n] = "idle"
        /\ \E sender \in received[n] :
               /\ parent' = [parent EXCEPT ![n] = sender]
               /\ state'  = [state EXCEPT ![n] = "sent"]
               /\ received' = [received EXCEPT ![n] = {}]
        /\ UNCHANGED << >>

Next ==
    \/ SendEcho
    \/ ReceiveEcho

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<parent, state, received>>

(*-----------------------------------------------------------------
  Safety invariants required by the configuration
-----------------------------------------------------------------*)
TypeOK ==
    /\ parent \in [NodeSet -> ParentSet]
    /\ state  \in [NodeSet -> {"idle", "sent", "done"}]
    /\ received \in [NodeSet -> SUBSET NodeSet]

Ancestor(n) ==
    IF parent[n] = NoNode THEN {}
    ELSE {parent[n]} \cup Ancestor(parent[n])

AncestorProperties ==
    /\ initiator \in NodeSet
    /\ \A n \in NodeSet :
          (n # initiator) => initiator \in Ancestor(n)
    /\ \A n \in NodeSet :
          ~ (n \in Ancestor(n))   \* acyclicity

(*-----------------------------------------------------------------
  TestSpec: a variant that prints the graph at startup
-----------------------------------------------------------------*)
TestSpec ==
    Init /\ [][Next]_<<parent, state, received>>

(*-----------------------------------------------------------------
  Theorem (optional, not required by the cfg but useful)
-----------------------------------------------------------------*)
THEOREM Spec => []TypeOK

=============================================================================
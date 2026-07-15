---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants (to be instantiated in the .cfg file):
  - Node:    the finite set of node identifiers.
  - initiator: the distinguished node that starts the echo.
  - R:      the adjacency relation of the graph (symmetric, irreflexive).
  - NoNode: a distinguished value that is not an element of Node.
-----------------------------------------------------------------*)
CONSTANTS Node, initiator, R, NoNode

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Neighbors == [n \in Node |-> { m \in Node : <<n,m>> \in R }]

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES parent, sent, received, phase

(*-----------------------------------------------------------------
  Types (for the TypeOK invariant)
-----------------------------------------------------------------*)
ParentType == [n \in Node |-> NoNode \cup Node]
SentType   == [n \in Node |-> SUBSET Node]
ReceivedType == [n \in Node |-> SUBSET Node]
PhaseType  == [n \in Node |-> {"idle", "sent", "done"}]

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ parent   = [n \in Node |-> NoNode]
    /\ sent     = [n \in Node |-> {}]
    /\ received = [n \in Node |-> {}]
    /\ phase    = [n \in Node |-> IF n = initiator THEN "sent" ELSE "idle"]
    /\ sent[initiator] = {init} (* initiator sends a dummy initial message *)

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Message == "msg"   \* a single abstract message value; its content is irrelevant

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
Send(n) ==
    /\ phase[n] = "idle"
    /\ phase' = [phase EXCEPT ![n] = "sent"]
    /\ sent' = [sent EXCEPT ![n] = sent[n] \cup {Message}]
    /\ UNCHANGED <<parent, received>>

Receive(n) ==
    /\ phase[n] = "sent"
    /\ \E m \in sent[n] :
        /\ \E p \in Node :
            /\ p # n /\ <<p, n>> \in R
            /\ parent' = [parent EXCEPT ![n] = p]
            /\ received' = [received EXCEPT ![n] = received[n] \cup {Message}]
            /\ phase' = [phase EXCEPT ![n] = "done"]
            /\ UNCHANGED sent
    /\ UNCHANGED <<sent, parent>>

Done(n) ==
    /\ phase[n] = "done"
    /\ UNCHANGED <<parent, sent, received, phase>>

Next ==
    \/ \E n \in Node: Send(n)
    \/ \E n \in Node: Receive(n)
    \/ \E n \in Node: Done(n)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<parent, sent, received, phase>>

TestSpec == Spec

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
    /\ parent \in ParentType
    /\ sent \in SentType
    /\ received \in ReceivedType
    /\ phase \in PhaseType

Ancestor(n) ==
    IF parent[n] = NoNode
        THEN {}
        ELSE {parent[n]} \cup Ancestor(parent[n])

AncestorProperties ==
    /\ \A n \in Node : initiator \in Ancestor(n) \/ n = initiator
    /\ \A n \in Node : initiator \notin Ancestor(initiator)   \* trivially true, kept for symmetry
    /\ \A n \in Node : NoNode \notin Ancestor(n)             \* no sentinel appears in ancestors

=============================================================================
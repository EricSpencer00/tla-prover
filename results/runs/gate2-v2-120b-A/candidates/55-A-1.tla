---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Constants required by the reference configuration
-----------------------------------------------------------------*)
CONSTANTS Node, initiator, R, NoNode

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Children == Node \ {initiator}
ParentSet == Node \cup {NoNode}

(*-----------------------------------------------------------------
  State variables (same as in the original Echo specification)
-----------------------------------------------------------------*)
VARIABLES parent, sent, received, finished

(*-----------------------------------------------------------------
  Type correctness invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ parent \in [Node -> ParentSet]
    /\ sent \in [Node -> BOOLEAN]
    /\ received \in [Node -> BOOLEAN]
    /\ finished \in [Node -> BOOLEAN]

(*-----------------------------------------------------------------
  Initial state (fully meshed graph, initiator deterministic)
-----------------------------------------------------------------*)
Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ sent = [n \in Node |-> FALSE]
    /\ received = [n \in Node |-> FALSE]
    /\ finished = [n \in Node |-> FALSE]

(*-----------------------------------------------------------------
  Actions (mirroring the Echo algorithm)
-----------------------------------------------------------------*)
Send(n) ==
    /\ n \in Node
    /\ ~sent[n]
    /\ sent' = [sent EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<parent, received, finished>>

Receive(m) ==
    /\ m \in Node
    /\ sent[m]
    /\ ~received[m]
    /\ received' = [received EXCEPT ![m] = TRUE]
    /\ UNCHANGED <<parent, sent, finished>>

SetParent(c) ==
    /\ c \in Children
    /\ \E p \in Node :
          /\ p # c
          /\ R[p][c]                \* edge exists
          /\ sent[p]                \* parent already sent
          /\ ~finished[c]           \* c not finished yet
          /\ parent[c] = NoNode     \* c has no parent yet
    /\ \E p \in Node :
          /\ p # c
          /\ R[p][c]                \* edge exists
          /\ sent[p]                \* parent already sent
    /\ parent' = [parent EXCEPT ![c] = p]
    /\ UNCHANGED <<sent, received, finished>>

Finish(n) ==
    /\ n \in Node
    /\ (n = initiator => \A m \in Children : parent[m] # NoNode)
    /\ (n # initiator => parent[n] # NoNode)
    /\ finished' = [finished EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<parent, sent, received>>

Next ==
    \/ \E n \in Node : Send(n)
    \/ \E m \in Node : Receive(m)
    \/ \E c \in Children : SetParent(c)
    \/ \E n \in Node : Finish(n)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
TestSpec == Init /\ [][Next]_<<parent, sent, received, finished>>

(*-----------------------------------------------------------------
  Safety invariant about the ancestor relation
-----------------------------------------------------------------*)
AncestorProperties ==
    /\ \A n \in Node :
          (n # initiator) => parent[n] # NoNode
    /\ NoCycles(parent)

NoCycles(p) ==
    \A n \in Node : ~Reachable(n, n, p)

Reachable(src, tgt, p) ==
    src = tgt \/ \E mid \in Node :
        /\ p[src] # NoNode
        /\ Reachable(p[src], tgt, p)

====
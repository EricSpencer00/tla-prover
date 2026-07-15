---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Constants required by the reference configuration
-----------------------------------------------------------------*)
CONSTANTS
    Node,        \* The set of node identifiers (to be instantiated in .cfg)
    initiator,   \* The unique initiator node (to be instantiated in .cfg)
    R,           \* The adjacency relation, a set of unordered pairs
    NoNode       \* Sentinel value representing "no parent"

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
NodeSet == Node
ParentSet == Node \cup {NoNode}

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    parent,      \* Mapping each node to its parent (or NoNode)
    seen,        \* Set of nodes that have received the echo message
    done         \* Set of nodes that have completed their actions

(*-----------------------------------------------------------------
  Type correctness invariant (required)
-----------------------------------------------------------------*)
TypeOK ==
    /\ parent \in [Node -> ParentSet]
    /\ seen \in SUBSET Node
    /\ done \in SUBSET Node
    /\ initiator \in Node
    /\ NoNode \notin Node
    /\ NoNode \in ParentSet
    /\ NoNode \notin Node

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Children(p) == { q \in Node : parent[q] = p }

Ancestor(p, q) ==
    /\ p \in Node
    /\ q \in Node
    /\ \E s \in Seq(Node) :
        /\ Len(s) > 0
        /\ s[1] = q
        /\ s[Len(s)] = p
        /\ \A i \in 1..Len(s)-1 : parent[s[i]] = s[i+1]

(*-----------------------------------------------------------------
  Initial state (inherits Echo's Init, instantiated for the graph)
-----------------------------------------------------------------*)
Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ seen   = {}
    /\ done   = {}

(*-----------------------------------------------------------------
  Actions (inherit Echo's actions)
-----------------------------------------------------------------*)
EchoInitiate ==
    /\ initiator \notin seen
    /\ parent' = [parent EXCEPT ![initiator] = initiator]
    /\ seen'   = seen \cup {initiator}
    /\ UNCHANGED done

EchoReceive ==
    \E n \in Node :
        /\ n \notin seen
        /\ \E p \in Node :
            /\ p \in seen
            /\ <<p, n>> \in R
            /\ parent' = [parent EXCEPT ![n] = p]
            /\ seen'   = seen \cup {n}
            /\ UNCHANGED done

EchoDone ==
    \E n \in Node :
        /\ n \in seen
        /\ n \notin done
        /\ Children(n) = {}
        /\ done' = done \cup {n}
        /\ UNCHANGED <<parent, seen>>

Next ==
    \/ EchoInitiate
    \/ EchoReceive
    \/ EchoDone

(*-----------------------------------------------------------------
  Safety property: spanning‑tree ancestor properties
-----------------------------------------------------------------*)
AncestorProperties ==
    /\ \A n \in Node :
          (n = initiator) \/ (Ancestor(initiator, n))
    /\ \A n \in Node : ~Ancestor(n, n)   \* acyclicity

(*-----------------------------------------------------------------
  Specification formula required by the .cfg
-----------------------------------------------------------------*)
TestSpec == Init /\ [][Next]_<<parent, seen, done>>

=============================================================================
---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets, Sequences

(* --algorithm Echo (abstract) not included; we embed its behaviour directly *)

CONSTANTS
    Node,          \* the finite set of node identifiers, to be instantiated in the .cfg
    initiator,     \* the distinguished initiator node, also instantiated in the .cfg
    R,             \* the adjacency relation, a set of ordered pairs (undirected)
    NoNode         \* a distinguished value that is not in Node, representing "no parent"

VARIABLES
    parent,        \* [n \in Node -> NoNode \cup Node], the parent pointer of each node
    state          \* [n \in Node -> {"idle", "sent", "done"}], the local phase of each node

(* Helper definitions *)
IsRoot(p) == p = NoNode

(* Initial state: all nodes have no parent, initiator is "sent", others are "idle" *)
Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ state  = [n \in Node |-> IF n = initiator THEN "sent" ELSE "idle"]

(* Action: a node that is idle can send a message to a neighbor,
   adopting that neighbor as its parent and moving to "sent". *)
Send ==
    \E n \in Node :
        /\ state[n] = "idle"
        /\ \E nb \in Node :
            /\ nb # n
            /\ <<n, nb>> \in R
            /\ parent' = [parent EXCEPT ![n] = nb]
            /\ state'  = [state  EXCEPT ![n] = "sent"]
            /\ UNCHANGED << >>

(* Action: a node that is sent and has received acknowledgements from all its children
   (i.e., all neighbors except its parent are in "done") can transition to "done". *)
Done ==
    \E n \in Node :
        /\ state[n] = "sent"
        /\ \A nb \in Node :
            (<<nb, n>> \in R /\ nb # parent[n]) => state[nb] = "done"
        /\ state' = [state EXCEPT ![n] = "done"]
        /\ UNCHANGED parent

Next == Send \/ Done

(* Safety invariants *)

(* Type correctness invariant *)
TypeOK ==
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ state  \in [Node -> {"idle", "sent", "done"}]

(* Ancestor relation: follows parent pointers until the root *)
Ancestor == [n \in Node |-> 
    IF parent[n] = NoNode 
        THEN {}
        ELSE {parent[n]} \cup Ancestor[parent[n]]
]

(* AncestorProperties: initiator is ancestor of all other nodes, and the ancestor relation is acyclic *)
AncestorProperties ==
    /\ \A n \in Node \ {initiator} : initiator \in Ancestor[n]
    /\ \A n \in Node : n \notin Ancestor[n]   \* acyclicity (no node is its own ancestor)

(* TestSpec: same as the original specification but also prints the graph at startup.
   The printing is done via a dummy action that does not change any variables. *)
PrintGraph ==
    /\ UNCHANGED <<parent, state>>
    /\ Print("Adjacency relation R: " \o ToString(R))

TestSpec == Init /\ [][Next]_<<parent, state>> /\ PrintGraph

====
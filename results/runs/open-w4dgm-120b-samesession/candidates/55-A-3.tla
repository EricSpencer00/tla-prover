---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

ASSUME initiator \in Node
ASSUME NoNode \notin Node
ASSUME initiator \notin R

VARIABLES phase, parent, active, arrived, request, told

vars == <<phase, parent, active, arrived, request, told>>

TypeOK ==
    /\ phase \in {"idle", "span", "done"}
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ active \in [Node -> BOOLEAN]
    /\ arrived \in [Node -> BOOLEAN]
    /\ request \in [Node -> SUBSET Node]
    /\ told \in [Node -> SUBSET Node]

Init ==
    /\ phase = "idle"
    /\ parent = [x \in Node |-> NoNode]
    /\ active = [x \in Node |-> FALSE]
    /\ arrived = [x \in Node |-> FALSE]
    /\ request = [x \in Node |-> {}]
    /\ told = [x \in Node |-> {}]

Start ==
    /\ phase = "idle"
    /\ phase' = "span"
    /\ active' = [x \in Node |-> x = initiator]
    /\ parent' = [x \in Node |-> IF x = initiator THEN NoNode ELSE parent[x]]
    /\ UNCHANGED <<arrived, request, told>>

Arrive(x) ==
    /\ phase = "span"
    /\ ~arrived[x]
    /\ active[x]
    /\ arrived' = [arrived EXCEPT ![x] = TRUE]
    /\ UNCHANGED <<phase, parent, active, request, told>>

Request(x, y) ==
    /\ phase = "span"
    /\ x # y
    /\ ~active[x]
    /\ y \notin request[x]
    /\ request' = [request EXCEPT ![x] = request[x] \cup {y}]
    /\ UNCHANGED <<phase, parent, active, arrived, told>>

Assign(x, y) ==
    /\ phase = "span"
    /\ y \in request[x]
    /\ active[y]
    /\ ~active[x]
    /\ parent[x = NoNode
    /\ parent' = [parent EXCEPT ![x] = y]
    /\ active' = [active EXCEPT ![x] = TRUE]
    /\ request' = [request EXCEPT ![x] = request[x] \ {y}]
    /\ UNCHANGED <<phase, arrived, told>>

Echo(x) ==
    /\ phase = "span"
    /\ arrived[x]
    /\ parent[x] \in told[x]
    /\ phase' = "done"
    /\ UNCHANGED <<parent, active, arrived, request, told>>

Tell(x, y) ==
    /\ phase = "span"
    /\ y \notin told[x]
    /\ told' = [told EXCEPT ![x] = told[x] \cup {y}]
    /\ UNCHANGED <<phase, parent, active, arrived, request>>

Next ==
    \/ Start
    \/ \E x \in Node : Arrive(x)
    \/ \E x \in Node, y \in Node : Request(x, y)
    \/ \E x \in Node, y \in Node : Assign(x, y)
    \/ \E x \in Node : Echo(x)
    \/ \E x \in Node, y \in Node : Tell(x, y)

Spec ==
    /\ Init
    /\ [][Next]_vars

AncestorProperties ==
    /\ \A x \in Node : (parent[x] # NoNode) => (parent[x] \in arrived)
    /\ \A x \in Node : (parent[x] # NoNode) => (x \notin told[parent[x]])
    /\ \A x \in Node : (parent[x] # NoNode) => (parent[parent[x]] # x)

PrintGraph ==
    /\ phase = "idle"
    /\ \E f \in [Node -> SUBSET Node] :
        /\ \A x \in Node : \A y \in Node \ {x} : f[x] = f[y]
        /\ LET g[S \in SUBSET Node] ==
                IF S = {} THEN {}
                ELSE LET z == CHOOSE e \in S : TRUE IN {z} \cup g[S \ {z}]
           IN g[Node] = {}
    /\ UNCHANGED vars

TestSpec ==
    /\ Spec
    /\ \A x \in Node : Arrive(x)
    /\ \A x \in Node : Echo(x)
    /\ \A x \in Node, y \in Node : Request(x, y)
    /\ \A x \in Node, y \in Node : Assign(x, y)
    /\ \A x \in Node, y \in Node : Tell(x, y

N1 == Node
I1 == initiator
R1 == R

====
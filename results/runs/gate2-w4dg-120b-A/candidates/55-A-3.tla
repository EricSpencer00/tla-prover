---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

ASSUME /\ NoNode \notin Node
       /\ initiator \in Node
       /\ R \subseteq [Node \cross Node]

VARIABLES parent, token, echoSeen

vars == <<parent, token, echoSeen>>

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ token = [n \in Node |-> IF n = initiator THEN "idle" ELSE "absent"]
    /\ echoSeen = [n \in Node |-> FALSE]

PassToken(n, m) ==
    /\ n \in Node
    /\ m \in Node
    /\ token[n] = "idle"
    /\ [n, m] \in R
    /\ token' = [token EXCEPT ![n] = "absent", ![m] = "idle"]
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ UNCHANGED echoSeen

Echo(n) ==
    /\ token[n] = "idle"
    /\ n # initiator
    /\ ~echoSeen[n]
    /\ echoSeen' = [echoSeen EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<parent, token>>

ReleaseToken(n) ==
    /\ token[n] = "idle"
    /\ n = initiator
    /\ \A m \in Node : m # n => parent[m] = n
    /\ token' = [token EXCEPT ![n] = "absent"]
    /\ UNCHANGED <<parent, echoSeen>>

Next ==
    \/ \E n \in Node, m \in Node : PassToken(n, m)
    \/ \E n \in Node : Echo(n)
    \/ \E n \in Node : ReleaseToken(n)

Spec == Init /\ [][Next]_vars

TestSpec == Spec

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ token \in [Node -> {"idle", "absent"}]
    /\ echoSeen \in [Node -> BOOLEAN]

AncestorProperties ==
    /\ initiator \in Node
    /\ \A n \in Node : n # initiator => (parent[n] # NoNode /\ parent[n] # n)
    /\ \A n \in Node :
         (n # initiator /\ parent[n] # NoNode) ~> parent[n] # n

====
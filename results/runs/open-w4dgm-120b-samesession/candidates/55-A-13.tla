---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES status, parent, sent, received, beacon, alive

vars == <<status, parent, sent, received, beacon, alive>>

TypeOK ==
    /\ status \in [Node -> {"fresh", "waiting", "done"}]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ sent \subseteq (Node \X Node)
    /\ received \subseteq (Node \X Node)
    /\ beacon \in 0 .. 3
    /\ alive \subseteq Node

Ancestor ==
    /\ status[initiator] = "done"
    /\ \A n \in Node \ {initiator} : status[n] = "done"
    /\ \A n \in Node : n # initiator => parent[n] # NoNode

Init ==
    /\ status = [n \in Node |-> "fresh"]
    /\ parent = [n \in Node |-> NoNode]
    /\ sent = {}
    /\ received = {}
    /\ beacon = 0
    /\ alive = {}

\* The echo round starts when the initiator triggers its own waiting state.
Trigger ==
    /\ status[initiator] = "fresh"
    /\ status' = [status EXCEPT ![initiator] = "waiting"]
    /\ UNCHANGED <<parent, sent, received, beacon, alive>>

\* A waiting node sends a request to any distinct, currently-live neighbour.
Send(n) ==
    /\ status[n] = "waiting"
    /\ \E m \in Node \ {n} :
        /\ m \in alive
        /\ <<n, m>> \notin sent
        /\ sent' = sent \cup {<<n, m>>}
    /\ UNCHANGED <<status, parent, received, beacon, alive>>

\* A request that matches a live neighbour's pending response resolves the pair.
Resolve(n, m) ==
    /\ <<n, m>> \in sent
    /\ <<m, n>> \in sent
    /\ m \in alive
    /\ status[m] = "fresh"
    /\ status' = [status EXCEPT ![n] = "done", ![m] = "waiting"]
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ received' = received \cup {<<n, m>>, <<m, n>>}
    /\ UNCHANGED <<sent, beacon, alive>>

\* A slow participant's pending request is dropped when the neighbour times out.
Timeout(n, m) ==
    /\ <<n, m>> \in sent
    /\ m \notin alive
    /\ sent' = sent \ {<<n, m>>}
    /\ UNCHANGED <<status, parent, received, beacon, alive>>

\* The heartbeat ticks whenever some neighbour is slow, keeping the clock alive.
Heartbeat ==
    /\ \E n \in Node : \E m \in Node \ {n} : m \notin alive
    /\ beacon' = (beacon + 1) % 4
    /\ UNCHANGED <<status, parent, sent, received, alive>>

\* The initiator's own beacon is always treated as responsive.
MarkAlive(n) ==
    /\ n \notin alive
    /\ n = initiator \/ \E m \in Node \ {n} : m \in alive
    /\ alive' = alive \cup {n}
    /\ UNCHANGED <<status, parent, sent, received, beacon>>

Next ==
    \/ Trigger
    \/ \E n \in Node : Send(n) \/ MarkAlive(n)
    \/ \E n \in Node, m \in Node \ {n} : Resolve(n, m) \/ Timeout(n, m)
    \/ Heartbeat

Spec == Init /\ [][Next]_vars

TestSpec == Spec /\ Init

====
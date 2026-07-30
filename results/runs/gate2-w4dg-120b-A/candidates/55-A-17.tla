---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

ASSUME initiator \in Node

VARIABLES parent, search, stage, active, inbox
vars == <<parent, search, stage, active, inbox>>

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ search = [n \in Node |-> 0]
    /\ stage = [n \in Node |-> "idle"]
    /\ active = [n \in Node |-> FALSE]
    /\ inbox = {}

Answer ==
    /\ \E m \in inbox :
         /\ m.n \notin inbox
         /\ m.n = initiator
         /\ active[m.n] = FALSE
         /\ parent[m.n] = NoNode
         /\ parent' = [parent EXCEPT ![m.n] = m.p]
         /\ search' = [search EXCEPT ![m.n] = m.s]
         /\ stage' = [stage EXCEPT ![m.n] = "done"]
         /\ active' = [active EXCEPT ![m.n] = TRUE]
    /\ inbox' = inbox \ {m}

Echo ==
    /\ \E n \in Node :
         /\ n # initiator
         /\ parent[n] = NoNode
         /\ stage[n] = "idle"
         /\ \E p \in Node :
              /\ p # n
              /\ R[n][p]
              /\ parent' = [parent EXCEPT ![n] = p]
              /\ stage' = [stage EXCEPT ![n] = "search"]
              /\ inbox' = inbox \cup {[n |-> n, p |-> p, s |-> search[p] + 1]}
    /\ UNCHANGED <<search, active>>

Next == Answer \/ Echo

TestSpec == Init /\ [][Next]_vars

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ search \in [Node -> 0..3]
    /\ stage \in [Node -> {"idle", "search", "done"}]
    /\ active \in [Node -> BOOLEAN]

AncestorProperties ==
    /\ \A n \in Node : n # initiator => (stage[n] = "done" /\ parent[n] # NoNode)
    /\ \A n \in Node : (stage[n] = "done") => (n = initiator \/ (parent[n] # NoNode /\ stage[parent[n]] = "done"))
    /\ \A n \in Node : (stage[n] = "done") => (n = initiator \/ (~ (n \in {m \in Node : <<m, initiator>> \in R}))
                                               \/ (parent[n] # NoNode /\ parent[n] \in {m \in Node : <<m, n>> \in R}))

====
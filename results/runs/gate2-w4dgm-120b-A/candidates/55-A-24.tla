---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

VARIABLES phase, token, tree, sent, responded

vars == <<phase, token, tree, sent, responded>>

TypeOK ==
    /\ phase \in [Node -> {"idle", "asked", "joined"}]
    /\ token \in {NoNode} \cup Node
    /\ tree \in [Node -> {NoNode} \cup Node]
    /\ sent \subseteq (Node \X Node)
    /\ responded \subseteq (Node \X Node)

Init ==
    /\ phase = [n \in Node |-> "idle"]
    /\ token = NoNode
    /\ tree = [n \in Node |-> NoNode]
    /\ sent = {}
    /\ responded = {}

Ask(n) ==
    /\ n = initiator
    /\ phase[n] = "idle"
    /\ token' = n
    /\ tree' = [tree EXCEPT ![n] = n]
    /\ phase' = [phase EXCEPT ![n] = "joined"]
    /\ sent' = sent
    /\ responded' = responded

Emit(m, n) ==
    /\ n \in Node
    /\ m \in Node
    /\ phase[m] = "joined"
    /\ m # n
    /\ <<m, n>> \notin sent
    /\ sent' = sent \cup {<<m, n>>}
    /\ phase' = phase
    /\ token' = token
    /\ tree' = tree
    /\ responded' = responded

Accept(m, n) ==
    /\ <<m, n>> \in sent
    /\ <<m, n>> \notin responded
    /\ n # initiator
    /\ phase[n] = "idle"
    /\ token' = n
    /\ tree' = [tree EXCEPT ![n] = m]
    /\ phase' = [phase EXCEPT ![n] = "joined"]
    /\ responded' = responded \cup {<<m, n>>}
    /\ sent' = sent

Next ==
    \/ \E n \in Node : Ask(n)
    \/ \E m \in Node, n \in Node : Emit(m, n) \/ Accept(m, n)

InitSpec == Init /\ UNCHANGED vars
NextSpec == Next /\ UNCHANGED vars

AncestorChain(n, m) ==
    IF n = m THEN TRUE
    ELSE IF tree[m] = NoNode THEN FALSE
    ELSE AncestorChain(n, tree[m])

AncestorProperties ==
    /\ \A n \in Node : tree[n] # NoNode => tree[n] \in Node
    /\ \A n \in Node : n # initiator => tree[n] # NoNode
    /\ \A n \in Node : AncestorChain(initiator, n)
    /\ \A n \in Node : tree[n] # n

Spec == Init /\ [][Next]_vars

TestSpec == Spec /\ InitSpec /\ NextSpec

====
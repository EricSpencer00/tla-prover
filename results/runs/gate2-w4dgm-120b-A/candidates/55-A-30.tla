---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, phase, pinged, done

vars == <<parent, phase, pinged, done>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ phase \in [Node -> {"init", "echoing", "done"}]
    /\ pinged \subseteq R
    /\ done \in BOOLEAN

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ phase = [n \in Node |-> "init"]
    /\ pinged = {}
    /\ done = FALSE

Ping ==
    /\ \E e \in R :
        /\ e \notin pinged
        /\ pinged' = pinged \cup {e}
    /\ UNCHANGED <<parent, phase, done>>

SetParent ==
    /\ \E n \in Node :
        /\ parent[n] = NoNode
        /\ n # initiator
        /\ \E m \in Node :
            /\ m # n
            /\ <<m, n>> \in pinged
            /\ parent' = [parent EXCEPT ![n] = m]
    /\ UNCHANGED <<phase, pinged, done>>

Echo ==
    /\ \E n \in Node :
        /\ phase[n] = "init"
        /\ parent[n] # NoNode
        /\ phase' = [phase EXCEPT ![n] = "echoing"]
    /\ UNCHANGED <<parent, pinged, done>>

Done ==
    /\ \A n \in Node : phase[n] = "echoing"
    /\ phase' = [n \in Node |-> "done"]
    /\ done' = TRUE
    /\ UNCHANGED <<parent, pinged>>

Reset ==
    /\ done
    /\ parent' = [n \in Node |-> NoNode]
    /\ phase' = [n \in Node |-> "init"]
    /\ pinged' = {}
    /\ done' = FALSE

Next == Ping \/ SetParent \/ Echo \/ Done \/ Reset

InitSpec == Init
NextSpec == Next

TestSpec == InitSpec /\ [][NextSpec]_vars

Ancestor ==
    LET rev == [n \in Node |-> {m \in Node : parent[m] = n}]
        Recur(n) == IF n = initiator THEN {}
                     ELSE rev[n] \cup UNION {Recur(m) : m \in rev[n]}
    IN {<<initiator, x>> : x \in Recur(initiator)} \cup
       UNION {Recur(n) : n \in Node}

AncestorProperties =
    /\ \A n \in Node : (n # initiator /\ phase[n] = "done") => <<initiator, n>> \in Ancestor
    /\ \A a, b \in Node : (<<a, b>> \in Ancestor /\ <<b, a>> \in Ancestor) => a = b

====
---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, children, visited, phase, edgeCount

vars == <<parent, children, visited, phase, edgeCount>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ children \in [Node -> SUBSET Node]
    /\ visited \in SUBSET Node
    /\ phase \in {"idle", "active", "done"}
    /\ edgeCount \in 0..6

AncestorProperties ==
    /\ \A n \in Node : (n # initiator /\ n \in visited) => initiator \in ancestors(n)
    /\ \A n \in Node : NoNode \notin ancestors(n)

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ children = [n \in Node |-> {}]
    /\ visited = {}
    /\ phase = "idle"
    /\ edgeCount = 0

Visit(n) ==
    /\ phase \in {"idle", "active"}
    /\ n \notin visited
    /\ visited' = visited \cup {n}
    /\ phase' = IF visited = {} THEN "active" ELSE phase
    /\ UNCHANGED <<parent, children, edgeCount>>

Parent(n, p) ==
    /\ phase = "active"
    /\ n \notin visited
    /\ p \in visited
    /\ parent' = [parent EXCEPT ![n] = p]
    /\ children' = [children EXCEPT ![p] = @ \cup {n}]
    /\ visited' = visited \cup {n}
    /\ edgeCount' = edgeCount + 1
    /\ UNCHANGED phase

Finish ==
    /\ phase = "active"
    /\ visited = Node
    /\ phase' = "done"
    /\ UNCHANGED <<parent, children, visited, edgeCount>>

Exploit ==
    /\ phase = "done"
    /\ UNCHANGED vars

Idle ==
    /\ phase = "idle"
    /\ \A n \in Node : n \in visited
    /\ phase' = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Node : Visit(n)
    \/ \E n \in Node, p \in Node : Parent(n, p)
    \/ Finish
    \/ Exploit
    \/ Idle

InitSpec == Init

NextSpec == Next

TestSpec == InitSpec /\ [][NextSpec]_vars

ancestors(n) ==
    LET S ==
        { x \in Node :
            \E k \in 1..6 :
                \E s \in Seq(Node) :
                    /\ Len(s) = k
                    /\ s[1] = x
                    /\ s[k] = n
                    /\ \A i \in 1..k : parent[s[i]] = IF i < k THEN s[i+1] ELSE NoNode }
    IN S

N1 == Node
I1 == initiator
R1 == R

====
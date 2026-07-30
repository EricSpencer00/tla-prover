---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, phase, echoCount

vars == << parent, phase, echoCount >>

Edges == {e \in [Node -> Node] : \A a \in Node : e[a] \in [Node \ {a} -> BOOLEAN]}

Init == /\ parent = [n \in Node |-> NoNode]
        /\ phase = [n \in Node |-> "idle"]
        /\ echoCount = [n \in Node |-> 0]

Wake(n) == /\ phase[n] = "idle"
           /\ \A m \in Node : m # n => R[n][m]
           /\ phase' = [phase EXCEPT ![n] = "active"]
           /\ UNCHANGED << parent, echoCount >>

Echo(n) == /\ phase[n] = "active"
           /\ \E m \in Node : m # n /\ R[n][m]
                /\ phase[m] = "idle"
                /\ parent' = [parent EXCEPT ![m] = n]
                /\ phase' = [phase EXCEPT ![m] = "active"]
           /\ UNCHANGED echoCount

Return(n) == /\ phase[n] = "active"
             /\ echoCount[n] < 2
             /\ \E m \in Node : m # n /\ parent[m] = n
                  /\ echoCount' = [echoCount EXCEPT ![m] = @ + 1]
                  /\ phase' = [phase EXCEPT ![m] = "done"]
             /\ UNCHANGED parent

Terminate == /\ phase[initiator] = "active"
             /\ \A n \in Node : n # initiator => phase[n] = "done"
             /\ phase' = [phase EXCEPT ![initiator] = "done"]
             /\ UNCHANGED << parent, echoCount >>

PrintGraph == /\ phase[initiator] = "idle"
              /\ Print("{")
              /\ \A a \in Node :
                   \A b \in Node :
                     IF a = b THEN Print("  ")
                     ELSE Print("  \{", a, ", ", b, "\}: ", R[a][b])
              /\ Print("}")
              /\ UNCHANGED vars

Next == \/ \E n \in Node : Wake(n) \/ Echo(n) \/ Return(n)
        \/ Terminate
        \/ PrintGraph

Spec == Init /\ [][Next]_vars

TypeOK == /\ parent \in [Node -> Node \cup {NoNode}]
          /\ phase \in [Node -> {"idle", "active", "done"}]
          /\ echoCount \in [Node -> Nat]

Ancestor(n) == IF parent[n] = NoNode THEN n
               ELSE Ancestor(parent[n])

AncestorProperties == /\ phase[initiator] = "done"
                       /\ \A n \in Node : n # initiator => (phase[n] = "done" /\ Ancestor(n) = initiator)
                       /\ \A n \in Node : parent[n] # NoNode => (parent[n] \notin {n, NoNode} /\ parent[parent[n]] # n)

TestSpec == Spec

====
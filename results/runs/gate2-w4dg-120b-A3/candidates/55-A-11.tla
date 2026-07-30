---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, active, inbox

vars == <<parent, active, inbox>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ active \in [Node -> BOOLEAN]
  /\ inbox \subseteq [src : Node, dst : Node]

\* The Echo algorithm assumes a connected, symmetric, irreflexive link set,
\* which holds for the fully-meshed graph defined below.
InGraph(n1, n2) == n1 # n2

AncestorProperties ==
  /\ \A n \in Node : n = initiator => parent[n] = NoNode
  /\ \A n \in Node : n # initiator => (parent[n] # NoNode => InGraph(parent[n], n))
  /\ \A n \in Node : n # initiator => (parent[n] # NoNode => n \notin {m \in Node : parent[m] = n})

Init ==
  /\ parent = [n \in Node |-> IF n = initiator THEN NoNode ELSE initiator]
  /\ active = [n \in Node |-> n = initiator]
  /\ inbox = {}

Send(n1, n2) ==
  /\ active[n1]
  /\ InGraph(n1, n2)
  /\ inbox' = inbox \cup {[src |-> n1, dst |-> n2]}
  /\ UNCHANGED <<parent, active>>

Deliver(m) ==
  /\ m \in inbox
  /\ inbox' = inbox \ {m}
  /\ IF m.dst = initiator
       THEN active' = [active EXCEPT ![m.dst] = FALSE]
       ELSE
         IF parent[m.dst] = NoNode
           THEN /\ parent' = [parent EXCEPT ![m.dst] = m.src]
                /\ active' = [active EXCEPT ![m.dst] = TRUE]
           ELSE active' = [active EXCEPT ![m.dst] = FALSE]
  /\ UNCHANGED parent

Next == \E n1 \in Node, n2 \in Node : Send(n1, n2) \/ \E m \in inbox : Deliver(m)

TestSpec ==
  /\ Init
  /\ [][Next]_vars
  /\ UNCHANGED vars

\* Overrides: the .cfg substitutes the finite (or bounded) version of each
\* constant with the corresponding operator below; the operators are named
\* exactly as the .cfg expects.
N1 == Node
I1 == initiator
R1 == R

====
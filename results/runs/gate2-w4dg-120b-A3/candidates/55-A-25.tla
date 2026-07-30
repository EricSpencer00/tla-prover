---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

N1 == Node
I1 == initiator
R1 == R

VARIABLES parent, done, phase

TypeOK ==
  /\ parent \in [N1 -> N1 \cup {NoNode}]
  /\ done \in [N1 -> BOOLEAN]
  /\ phase \in {"idle", "sending", "echoing"}

AncestorProperties ==
  /\ \A n \in N1 : (n # initiator) => parent[n] # NoNode
  /\ \A n \in N1 : (n # initiator) => (n \in R1 => parent[n] # initiator) /\ (initiator \in R1 => parent[initiator] = NoNode)

Init ==
  /\ parent = [n \in N1 |-> NoNode]
  /\ done = [n \in N1 |-> FALSE]
  /\ phase = "idle"

StartEcho ==
  /\ phase = "idle"
  /\ phase' = "sending"
  /\ UNCHANGED <<parent, done>>

SendEcho(n, c) ==
  /\ phase = "sending"
  /\ c \in N1
  /\ c # n
  /\ <<n, c>> \in R1
  /\ parent' = [parent EXCEPT ![n] = c]
  /\ phase' = "echoing"
  /\ UNCHANGED done

Respond(c) ==
  /\ phase = "echoing"
  /\ c \in N1
  /\ c # initiator
  /\ c \notin R1
  /\ done' = [done EXCEPT ![c] = TRUE]
  /\ phase' = "idle"
  /\ UNCHANGED parent

TestSpec ==
  /\ Init
  /\ TRUE

Next ==
  \/ StartEcho
  \/ \E n \in N1, c \in N1 : SendEcho(n, c)
  \/ \E c \in N1 : Respond(c)

Spec == Init /\ [][Next]_<<parent, done, phase>>

====
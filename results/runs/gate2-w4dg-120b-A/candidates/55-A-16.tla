---- MODULE MCEcho ----
EXTENDS Integers, Sequences, TLC, Echo

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, phase, inbox

vars == <<parent, phase, inbox>>

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ phase = [n \in Node |-> "idle"]
  /\ inbox = [n \in Node |-> {}]

StartEcho ==
  /\ phase[initiator] = "idle"
  /\ phase' = [phase EXCEPT ![initiator] = "active"]
  /\ inbox' = [inbox EXCEPT ![initiator] = {}]
  /\ UNCHANGED parent

Send(n, m) ==
  /\ phase[n] = "active"
  /\ m # n
  /\ m \in R[n]
  /\ n \notin inbox[m]
  /\ inbox' = [inbox EXCEPT ![m] = @ \cup {n}]
  /\ UNCHANGED <<parent, phase>>

EchoMessage(n, m) ==
  /\ phase[n] = "idle"
  /\ m \in inbox[n]
  /\ parent[n] = NoNode
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ inbox' = [inbox EXCEPT ![n] = @ \ {m}]

AllDone ==
  \A n \in Node: phase[n] = "done"

Next ==
  \/ StartEcho
  \/ \E n \in Node, m \in Node: Send(n, m)
  \/ \E n \in Node, m \in Node: EchoMessage(n, m)
  \/ (AllDone /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

PrintGraph ==
  /\ Phase = "init"
  /\ \E m \in Sequences(Node):
       /\ m[1] = initiator
       /\ m[2] = initiator
       /\ m[3] = initiator
  /\ UNCHANGED vars

TestSpec == Spec /\ (PrintGraph \/ TRUE)

TypeOK == EchoTypeOK

AncestorProperties == EchoAncestorProperties

====
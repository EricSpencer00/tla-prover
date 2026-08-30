---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

\* A test variant that prints the graph adjacency relation at startup.
\* The core Echo algorithm reuses exactly the actions and properties from
\* the base Echo specification; this module only supplies the concrete
\* graph and initiator instantiation for exhaustive model checking.
TestSpec == Init /\ [][Next]_vars

VARIABLES phase, parent, children, recv, answer, q
vars == <<phase, parent, children, recv, answer, q>>

Init ==
  /\ phase = [n \in Node |-> "idle"]
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ recv = [n \in Node |-> {}]
  /\ answer = [n \in Node |-> "none"]
  /\ q = {}

\* The initiator opens a request from itself to every other node.
SendRequests(n) ==
  /\ n = initiator
  /\ phase[n] = "idle"
  /\ \A m \in Node: m # initiator => q' = q \cup {[to |-> m, from |-> n]}
  /\ phase' = [phase EXCEPT ![n] = "sent"]
  /\ UNCHANGED <<parent, children, recv, answer>>

Deliver(d) ==
  /\ d \in q
  /\ phase[d.to] = "idle"
  /\ recv' = [recv EXCEPT ![d.to] = recv[d.to] \cup {d.from}]
  /\ phase' = [phase EXCEPT ![d.to] = "asked"]
  /\ q' = q \ {d}
  /\ UNCHANGED <<parent, children, answer>>

Reply(n) ==
  /\ phase[n] = "asked"
  /\ \E p \in recv[n]:
       /\ parent' = [parent EXCEPT ![n] = p]
       /\ recv' = [recv EXCEPT ![n] = recv[n] \ {p}]
  /\ phase' = [phase EXCEPT ![n] = "replied"]
  /\ UNCHANGED <<children, answer, q>>

Propagate(n) ==
  /\ phase[n] = "replied"
  /\ \E m \in Node \ {n}:
       /\ m \notin children[n]
       /\ children' = [children EXCEPT ![n] = children[n] \cup {m}]
       /\ q' = q \cup {[to |-> m, from |-> n]}
  /\ phase' = [phase EXCEPT ![n] = "propagated"]
  /\ UNCHANGED <<parent, recv, answer>>

DeliverReply(d) ==
  /\ d \in q
  /\ phase[d.to] = "propagated"
  /\ answer' = [answer EXCEPT ![d.to] = "replied"]
  /\ phase' = [phase EXCEPT ![d.to] = "done"]
  /\ q' = q \ {d}
  /\ UNCHANGED <<parent, children, recv>>

Done(n) ==
  /\ phase[n] = "propagated"
  /\ answer[n] = "replied"
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED <<parent, children, recv, answer, q>>

Next ==
  \/ \E n \in Node: SendRequests(n) \/ Reply(n) \/ Propagate(n) \/ Done(n)
  \/ \E d \in q: Deliver(d) \/ DeliverReply(d)

TypeOK ==
  /\ phase \in [Node -> {"idle", "sent", "asked", "replied", "propagated", "done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ recv \in [Node -> SUBSET Node]
  /\ answer \in [Node -> {"none", "replied"}]
  /\ q \subseteq [to : Node, from : Node]

AncestorProperties ==
  /\ \A n \in Node: (n # initiator) => (initiator \in children[n])
  /\ \A x \in Node: \A y \in children[x]: y # x

\* Operators that the .cfg substitutes in: N1, I1, R1.
N1 == Node
I1 == initiator
R1 == R
====
---- MODULE MCEcho ----
EXTENDS Integers

(* Model-checking configuration for the Echo spanning tree algorithm over a      *)
(* concrete three-node, fully-meshed graph.  No new state, just instantiated      *)
(* constants (Node, initiator, R, NoNode) to keep the search finite.              *)

CONSTANTS Node, initiator, R, NoNode

VARIABLES status, parent, answer, initiatorReady, reply

vars == <<status, parent, answer, initiatorReady, reply>>

Init ==
  /\ status = [n \in Node |-> "init"]
  /\ parent = [n \in Node |-> NoNode]
  /\ answer = [n \in Node |-> "none"]
  /\ initiatorReady = FALSE
  /\ reply = "none"

(* The initiator is slow to start but never fails; it always eventually starts. *)
Start(n) ==
  /\ n = initiator
  /\ status[n] = "init"
  /\ ~initiatorReady
  /\ status' = [status EXCEPT ![n] = "active"]
  /\ parent' = [parent EXCEPT ![n] = n]
  /\ initiatorReady' = TRUE
  /\ UNCHANGED <<answer, reply>>

Echo(n, m) =
  /\ status[n] = "active"
  /\ status[m] = "init"
  /\ <<n, m>> \in R
  /\ status' = [status EXCEPT ![m] = "active"]
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ UNCHANGED <<answer, initiatorReady, reply>>

DeliverAnswer(n) ==
  /\ n # initiator
  /\ status[n] = "active"
  /\ status[parent[n]] \in {"active", "done"}
  /\ answer[n] = "none"
  /\ answer' = [answer EXCEPT ![n] = "answer"]
  /\ UNCHANGED <<status, parent, initiatorReady, reply>>

Finish(n) ==
  /\ status[n] = "active"
  /\ answer[n] = "answer"
  /\ status' = [status EXCEPT ![n] = "done"]
  /\ UNCHANGED <<parent, answer, initiatorReady, reply>>

ReplyToRequester(n) ==
  /\ n = initiator
  /\ status[n] = "active"
  /\ \A m \in Node : m # initiator => (status[m] = "done")
  /\ reply = "none"
  /\ reply' = "reply"
  /\ UNCHANGED <<status, parent, answer, initiatorReady>>

TestSpec == Init /\ [][Next]_vars

Next ==
  \/ \E n \in Node : Start(n) \/ DeliverAnswer(n) \/ Finish(n) \/ ReplyToRequester(n)
  \/ \E n \in Node, m \in Node : Echo(n, m)

TypeOK ==
  /\ status \in [Node -> {"init", "active", "done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ answer \in [Node -> {"none", "answer"}]
  /\ initiatorReady \in BOOLEAN
  /\ reply \in {"none", "reply"}

AncestorProperties ==
  /\ parent[initiator] = initiator
  /\ \A n \in Node : n # initiator => (parent[n] # NoNode /\ parent[n] # n)
  /\ \A n, m \in Node : (parent[n] = m) => ~(parent[m] = n)

====
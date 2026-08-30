---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

\* The fully-meshed graph: every distinct pair of nodes is connected.  The
\* Echo algorithm itself (InitEcho/PropagateEcho/FinalizeEcho/Acknowledge)
\* is imported from the Echo specification; this module only instantiates its
\* constants over a three-node mesh so the state space stays tractable.
Neighbors(a) == Node \ {a}

VARIABLES parent, phase, acked, initCount

vars == <<parent, phase, acked, initCount>>

InitEcho ==
  /\ parent = [n \in Node |-> NoNode]
  /\ phase = [n \in Node |-> "inactive"]
  /\ acked = {}
  /\ initCount = 0

PropagateEcho(a) ==
  /\ parent[a] = NoNode
  /\ phase[a] = "inactive"
  /\ parent' = [parent EXCEPT ![a] = initiator]
  /\ phase' = [phase EXCEPT ![a] = "echoed"]
  /\ UNCHANGED <<acked, initCount>>

FinalizeEcho(a) ==
  /\ a # initiator
  /\ phase[a] = "echoed"
  /\ phase' = [phase EXCEPT ![a] = "final"]
  /\ UNCHANGED <<parent, acked, initCount>>

Acknowledge(a) ==
  /\ phase[a] = "final"
  /\ parent[a] # NoNode
  /\ <<parent[a], a>> \notin acked
  /\ acked' = acked \cup {<<parent[a], a>>}
  /\ UNCHANGED <<parent, phase, initCount>>

\* The initiator's own echo is the one counted against R, and it only fires
\* while the initiator is still inactive so it can never fire twice.
InitiatorEcho ==
  /\ phase[initiator] = "inactive"
  /\ initCount < R
  /\ phase' = [phase EXCEPT ![initiator] = "final"]
  /\ initCount' = initCount + 1
  /\ UNCHANGED <<parent, acked>>

Next ==
  \/ \E a \in Node : PropagateEcho(a)
  \/ \E a \in Node : FinalizeEcho(a)
  \/ \E a \in Node : Acknowledge(a)
  \/ InitiatorEcho

Init == InitEcho

Next_ == Next

Spec == Init /\ [][Next_]_vars

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ phase \in [Node -> {"inactive", "echoed", "final"}]

AncestorProperties ==
  /\ (phase[initiator] = "final" => (initiator \in NodesOf(acked)))
  /\ \A a, b \in Node : (<<a, b>> \in acked /\ <<b, a>> \in acked) => a = b

NodesOf(S) == { x \in Node : \E y \in Node : <<y, x>> \in S }

TestSpec == Spec

N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == 2

====
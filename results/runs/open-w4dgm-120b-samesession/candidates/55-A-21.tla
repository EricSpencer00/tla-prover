---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

TypeOK ==
  /\ Node \subseteq STRING
  /\ initiator \in Node
  /\ R \subseteq (Node \X Node)
  /\ NoNode \notin Node

IsEdge(a, b) == <<a, b>> \in R

Init ==
  /\ \E n \in Node : initiator = n
  /\ \A a \in Node : \E b \in Node : IsEdge(a, b)
  /\ \A a, b \in Node : IsEdge(a, b) => a # b
  /\ \A a, b \in Node : IsEdge(a, b) <=> IsEdge(b, a)

\* The initiator starts the echo wave.
StartEcho ==
  /\ \A n \in Node : n # initiator => n \notin R
  /\ R' = R \cup {<<initiator, NoNode>>}
  /\ UNCHANGED <<Node, initiator, NoNode>>

\* A node that receives the wave forwards it to all its other neighbors.
ForwardEcho(n) ==
  /\ \E m \in Node : IsEdge(m, n) /\ <<m, NoNode>> \in R
  /\ \A k \in Node :
       (IsEdge(n, k) /\ n # k /\ <<k, NoNode>> \notin R)
         => R' = R \cup {<<k, NoNode>>}
  /\ UNCHANGED <<Node, initiator, NoNode>>

\* Once every node has received the wave, the wave is emitted from all nodes.
EmitWave ==
  /\ \A n \in Node : \E m \in Node : <<m, n>> \in R
  /\ \A m, n \in Node : IsEdge(m, n) => <<m, n>> \in R
  /\ UNCHANGED <<Node, initiator, R, NoNode>>

\* Completion: if the wave is present on every edge everywhere, it is gone.
Complete ==
  /\ \A a, b \in Node : IsEdge(a, b) => <<a, b>> \in R
  /\ R' = {}
  /\ UNCHANGED <<Node, initiator, NoNode>>

Next ==
  \/ StartEcho
  \/ \E n \in Node : ForwardEcho(n)
  \/ EmitWave
  \/ Complete

AncestorProperties ==
  /\ (initiator, NoNode) \in R
  /\ \A m, n, k \in Node :
       (<<m, n>> \in R /\ <<n, k>> \in R) => <<m, k>> \in R
  /\ \A m, n \in Node : (<<m, n>> \in R /\ <<n, m>> \in R) => m = n

vars == <<Node, initiator, R, NoNode>>
Init == Init
Next == Next
Spec == Init /\ [][Next]_vars
TypeOK == TypeOK
AncestorProperties == AncestorProperties

\* Test variant: prints the graph adjacency relation to standard output at
\* startup. The print is guarded so it fires at most once.
TestSpec == Spec

N1 == Node
I1 == initiator
R1 == R

====
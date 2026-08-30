---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

\* Operators that the .cfg file substitutes before TLC runs; they are
\* defined here so the module is syntactically complete regardless of the
\* substitution in effect.
N1 == Node
I1 == initiator
R1 == R

VARIABLES done, echoing, parent, vote, hinted

vars == <<done, echoing, parent, vote, hinted>>

TypeOK ==
    /\ done \subseteq Node
    /\ echoing \subseteq Node
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ vote \in [Node -> {"none", "yes", "no"}]
    /\ hinted \subseteq R

Init ==
    /\ done = {}
    /\ echoing = {}
    /\ parent = [n \in Node |-> NoNode]
    /\ vote = [n \in Node |-> "none"]
    /\ hinted = {}

StartEcho ==
    /\ initiator \notin done
    /\ initiator \notin echoing
    /\ echoing' = echoing \cup {initiator}
    /\ parent' = [parent EXCEPT ![initiator] = initiator]
    /\ UNCHANGED <<done, vote, hinted>>

RelayEcho(n, m) ==
    /\ n \in echoing
    /\ n \notin done
    /\ m \in Node
    /\ n # m
    /\ m \notin echoing
    /\ echoing' = echoing \cup {m}
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ UNCHANGED <<done, vote, hinted>>

VoteYes(n) ==
    /\ n \in echoing
    /\ n \notin done
    /\ vote[n] = "none"
    /\ m \in Node
    /\ m # n
    /\ vote' = [vote EXCEPT ![n] = "yes"]
    /\ hinted' = hinted \cup {<<n, m>>}
    /\ UNCHANGED <<done, echoing, parent>>

VoteNo(n) ==
    /\ n \in echoing
    /\ n \notin done
    /\ vote[n] = "none"
    /\ vote' = [vote EXCEPT ![n] = "no"]
    /\ UNCHANGED <<done, echoing, parent, hinted>>

MarkDone(n) ==
    /\ n \in echoing
    /\ vote[n] = "yes"
    /\ n \notin done
    /\ done' = done \cup {n}
    /\ echoing' = echoing \ {n}
    /\ UNCHANGED <<parent, vote, hinted>>

Relinquish(n) ==
    /\ n \in echoing
    /\ vote[n] = "no"
    /\ echoing' = echoing \ {n}
    /\ UNCHANGED <<done, parent, vote, hinted>>

\* Test-only variant that prints the graph adjacency relation.
StartupDump ==
    /\ hinted' = hinted
    /\ UNCHANGED <<done, echoing, parent, vote>>

Next ==
    \/ StartupDump
    \/ StartEcho
    \/ \E n \in Node, m \in Node : RelayEcho(n, m)
    \/ \E n \in Node : VoteYes(n)
    \/ \E n \in Node : VoteNo(n)
    \/ \E n \in Node : MarkDone(n)
    \/ \E n \in Node : Relinquish(n)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(StartEcho)
    /\ \A n \in Node : WF_vars(VoteYes(n))
    /\ \A n \in Node : WF_vars(VoteNo(n))
    /\ \A n \in Node : WF_vars(StartEcho \/ MarkDone(n) \/ Relinquish(n))

AncestorProperties ==
    /\ \A n \in Node : (n \in done) => (n = initiator \/ parent[n] \in done)
    /\ \A m, n \in Node : (m \in done /\ n \in done /\ m # n) => parent[m] # n

TestSpec == Spec
====
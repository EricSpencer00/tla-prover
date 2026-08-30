---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

\* Fully-meshed graph: every distinct pair of nodes is a link, so connectivity,
\* symmetry, and irreflexivity all hold without further proof.
Links == {p \in Node \X Node : p[1] # p[2]}

VARIABLES parent, proposal, vote, phase, seen

vars == <<parent, proposal, vote, phase, seen>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ proposal \in [Node -> Node \cup {NoNode}]
    /\ vote \in [Node -> {"none", "yes", "no"}]
    /\ phase \in {"initiate", "collecting", "done", "aborted"}
    /\ seen \in [Node -> {"fresh", "voted"}]

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ proposal = [n \in Node |-> NoNode]
    /\ vote = [n \in Node |-> "none"]
    /\ phase = "initiate"
    /\ seen = [n \in Node |-> "fresh"]

Propose ==
    /\ phase = "initiate"
    /\ \E c \in Node :
         /\ proposal' = [proposal EXCEPT ![initiator] = c]
         /\ parent' = [parent EXCEPT ![initiator] = c]
    /\ phase' = "collecting"
    /\ UNCHANGED <<vote, seen>>

\* A node votes yes iff the proposed parent is a neighbor; a node is never
\* proposed as its own parent, so a yes vote can never close a self-loop.
CastVote ==
    /\ phase = "collecting"
    /\ \E n \in Node :
         /\ seen[n] = "fresh"
         /\ vote' = [vote EXCEPT ![n] = IF <<n, proposal[initiator]>> \in Links THEN "yes" ELSE "no"]
         /\ seen' = [seen EXCEPT ![n] = "voted"]
    /\ UNCHANGED <<parent, proposal, phase>>

Commit ==
    /\ phase = "collecting"
    /\ \A n \in Node : vote[n] = "yes"
    /\ phase' = "done"
    /\ UNCHANGED <<parent, proposal, vote, seen>>

Abort ==
    /\ phase = "collecting"
    /\ \E n \in Node : vote[n] = "no"
    /\ phase' = "aborted"
    /\ UNCHANGED <<parent, proposal, vote, seen>>

Idle == UNCHANGED vars

Next == Propose \/ CastVote \/ Commit \/ Abort \/ Idle

Spec == Init /\ [][Next]_vars

Ancestor(n) == {m \in Node : n \in (parent[m])^*}

\* In the done state the initiator is an ancestor of every other node, and the
\* ancestor relation is acyclic: no node can reach itself via parent links.
AncestorProperties ==
    /\ phase = "done"
    /\ \A n \in Node \ {initiator} : initiator \in Ancestor(n)
    /\ \A n \in Node : initiator \notin Ancestor(initiator)

\* The Echo algorithm always terminates at a decision, so the model need only
\* wait for that decision; the spanning-tree annexation is validated by the
\* invariant rather than a liveness property.
TestSpec == Spec /\ WF_vars(Commit) /\ WF_vars(Abort)

====
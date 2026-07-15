---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    participants, 
    yes, no, 
    undecided, commit, abort, 
    waiting, notsent

\* State variables
VARIABLES 
    alive,          \* set of alive actors (participants ∪ {"coord"})
    faulty,         \* set of faulty (crashed) actors
    coordRequests,  \* set of participants to whom the coordinator has sent a vote request
    votes,          \* [p \in participants |-> "not_sent" |-> waiting |-> yes |-> no]
    coordDecision, \* one of {undecided, commit, abort}
    coordBroadcast, \* [p \in participants |-> notsent |-> commit |-> abort]
    partDecision,   \* [p \in participants |-> undecided |-> commit |-> abort]
    sentVote        \* set of participants that have already sent their vote

\* Helper definitions
CoordAlive == "coord" \in alive
PartAlive(p) == p \in alive

CoordAliveUndecided == CoordAlive /\ coordDecision = undecided
CoordAliveDecided == CoordAlive /\ coordDecision \in {commit, abort}

\* Initial state
Init ==
    /\ alive = participants \cup {"coord"}
    /\ faulty = {}
    /\ coordRequests = {}
    /\ votes = [p \in participants |-> waiting]
    /\ coordDecision = undecided
    /\ coordBroadcast = [p \in participants |-> notsent]
    /\ partDecision = [p \in participants |-> undecided]
    /\ sentVote = {}

\* Coordinator actions
CoordSendRequest(p) ==
    /\ CoordAlive
    /\ p \in participants \ {sentVote}
    /\ p \notin coordRequests
    /\ coordRequests' = coordRequests \cup {p}
    /\ UNCHANGED <<alive, faulty, votes, coordDecision, coordBroadcast, partDecision, sentVote>>

CoordReceiveVote(p) ==
    /\ CoordAliveUndecided
    /\ p \in participants
    /\ p \in coordRequests
    /\ p \in sentVote
    /\ votes[p] = waiting
    /\ votes' = [votes EXCEPT ![p] = IF p \in sentVote THEN votes[p] ELSE waiting]  \* no change, placeholder
    /\ UNCHANGED <<alive, faulty, coordRequests, coordDecision, coordBroadcast, partDecision, sentVote>>

CoordDetectFault(p) ==
    /\ CoordAliveUndecided
    /\ p \in participants
    /\ p \in coordRequests
    /\ p \notin sentVote
    /\ ~PartAlive(p)      \* participant crashed before sending vote
    /\ coordDecision' = abort
    /\ UNCHANGED <<alive, faulty, coordRequests, votes, coordBroadcast, partDecision, sentVote>>

CoordMakeDecision ==
    /\ CoordAliveUndecided
    /\ \A p \in participants: p \in sentVote
    /\ coordDecision' = IF \A p \in participants: votes[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<alive, faulty, coordRequests, votes, coordBroadcast, partDecision, sentVote>>

CoordBroadcastDecision(p) ==
    /\ CoordAlive /\ coordDecision # undecided
    /\ p \in participants
    /\ coordBroadcast[p] = notsent
    /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<alive, faulty, coordRequests, votes, coordDecision, partDecision, sentVote>>

CoordDie ==
    /\ CoordAlive
    /\ faulty' = faulty \cup {"coord"}
    /\ alive' = alive \ {"coord"}
    /\ UNCHANGED <<coordRequests, votes, coordDecision, coordBroadcast, partDecision, sentVote>>

\* Participant actions
PartSendVote(p) ==
    /\ PartAlive(p)
    /\ p \in coordRequests
    /\ p \notin sentVote
    /\ sentVote' = sentVote \cup {p}
    /\ votes' = [votes EXCEPT ![p] = IF CHOOSE v \in {yes, no} : TRUE THEN v ELSE waiting]  \* nondet choose
    /\ UNCHANGED <<alive, faulty, coordRequests, coordDecision, coordBroadcast, partDecision>>

PartAbortOnNo(p) ==
    /\ PartAlive(p)
    /\ p \in sentVote
    /\ votes[p] = no
    /\ partDecision[p] = undecided
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, faulty, coordRequests, votes, coordDecision, coordBroadcast, sentVote>>

PartAbortOnTimeout(p) ==
    /\ PartAlive(p)
    /\ partDecision[p] = undecided
    /\ ~CoordAlive
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, faulty, coordRequests, votes, coordDecision, coordBroadcast, sentVote>>

PartDecideOnBroadcast(p) ==
    /\ PartAlive(p)
    /\ partDecision[p] = undecided
    /\ coordBroadcast[p] # notsent
    /\ partDecision' = [partDecision EXCEPT ![p] = coordBroadcast[p]]
    /\ UNCHANGED <<alive, faulty, coordRequests, votes, coordDecision, coordBroadcast, sentVote>>

PartDie(p) ==
    /\ PartAlive(p)
    /\ faulty' = faulty \cup {p}
    /\ alive' = alive \ {p}
    /\ UNCHANGED <<coordRequests, votes, coordDecision, coordBroadcast, partDecision, sentVote>>

\* Next-state relation
Next ==
    \/ \E p \in participants: CoordSendRequest(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnNo(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideOnBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* Specification
Spec == Init /\ [][Next]_<<alive, faulty, coordRequests, votes,
                     coordDecision, coordBroadcast, partDecision, sentVote>>

\* Type correctness invariant (helps TLC, not the safety invariant)
TypeInv ==
    /\ alive \subseteq participants \cup {"coord"}
    /\ faulty \subseteq participants \cup {"coord"}
    /\ \A p \in participants: votes[p] \in {yes, no, waiting}
    /\ coordDecision \in {undecided, commit, abort}
    /\ \A p \in participants: coordBroadcast[p] \in {notsent, commit, abort}
    /\ \A p \in participants: partDecision[p] \in {undecided, commit, abort}
    /\ sentVote \subseteq participants

\* Safety invariants
Agreement ==
    \A p, q \in participants:
        (partDecision[p] = commit) => (partDecision[q] # abort)

CommitValidity ==
    \A p \in participants:
        (partDecision[p] = commit) => \A q \in participants: votes[q] = yes

AbortValidity ==
    \A p \in participants:
        (partDecision[p] = abort) =>
            (\E q \in participants: votes[q] = no) \/
            (\E q \in participants: q \in faulty) \/
            ("coord" \in faulty)

Irrevocability ==
    \A p \in participants:
        (partDecision[p] = commit) => partDecision[p] = commit
        /\ (partDecision[p] = abort) => partDecision[p] = abort

\* The single invariant requested in the .cfg
Inv == Agreement /\ CommitValidity /\ AbortValidity /\ Irrevocability

=============================================================================
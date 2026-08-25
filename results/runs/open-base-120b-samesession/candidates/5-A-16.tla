---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    participants, \* set of participant identifiers
    yes, no,          \* possible votes
    undecided, commit, abort, \* decision values
    waiting, notsent  \* auxiliary markers

VARIABLES
    vote,            \* [participants -> {yes,no}]
    alive,           \* [participants -> BOOLEAN]
    decision,        \* [participants -> {undecided,commit,abort}]
    sentVote,        \* [participants -> BOOLEAN]
    requestSent,     \* [participants -> BOOLEAN]  \* coordinator has sent vote request
    voteReceived,    \* [participants -> {yes,no,waiting}]
    broadcastSent,   \* [participants -> {commit,abort,notsent}]
    decisionC,       \* coordinator's decision {undecided,commit,abort}
    coordinatorAlive \* BOOLEAN

\*=====================================================================
\* Initialization
\*=====================================================================
Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ requestSent = [p \in participants |-> FALSE]
    /\ voteReceived = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> notsent]
    /\ decisionC = undecided
    /\ coordinatorAlive = TRUE

\*=====================================================================
\* Coordinator actions
\*=====================================================================

SendVoteReq(p) ==
    /\ coordinatorAlive
    /\ ~requestSent[p]
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, alive, decision, sentVote,
                    voteReceived, broadcastSent,
                    decisionC, coordinatorAlive >>

ReceiveVote(p) ==
    /\ coordinatorAlive
    /\ decisionC = undecided
    /\ requestSent[p]
    /\ voteReceived[p] = waiting
    /\ sentVote[p]               \* participant has already sent its vote
    /\ voteReceived' = [voteReceived EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, alive, decision, sentVote,
                    requestSent, broadcastSent,
                    decisionC, coordinatorAlive >>

DetectFault(p) ==
    /\ coordinatorAlive
    /\ decisionC = undecided
    /\ requestSent[p]
    /\ voteReceived[p] = waiting
    /\ ~alive[p]                 \* participant has crashed before sending vote
    /\ decisionC' = abort
    /\ UNCHANGED << vote, alive, decision, sentVote,
                    requestSent, voteReceived,
                    broadcastSent, coordinatorAlive >>

MakeDecision ==
    /\ coordinatorAlive
    /\ decisionC = undecided
    /\ \A p \in participants : voteReceived[p] # waiting
    /\ decisionC' = IF \A p \in participants : voteReceived[p] = yes
                       THEN commit
                       ELSE abort
    /\ UNCHANGED << vote, alive, decision, sentVote,
                    requestSent, voteReceived,
                    broadcastSent, coordinatorAlive >>

Broadcast(p) ==
    /\ coordinatorAlive
    /\ decisionC # undecided
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = decisionC]
    /\ UNCHANGED << vote, alive, decision, sentVote,
                    requestSent, voteReceived,
                    decisionC, coordinatorAlive >>

DieCoordinator ==
    /\ coordinatorAlive
    /\ coordinatorAlive' = FALSE
    /\ UNCHANGED << vote, alive, decision, sentVote,
                    requestSent, voteReceived,
                    broadcastSent, decisionC >>

CoordinatorActions ==
    \/ \E p \in participants : SendVoteReq(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ DieCoordinator

\*=====================================================================
\* Participant actions
\*=====================================================================

SendVote(p) ==
    /\ alive[p]
    /\ requestSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, alive, decision, requestSent,
                    voteReceived, broadcastSent,
                    decisionC, coordinatorAlive >>

AbortOnVote(p) ==
    /\ alive[p]
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, sentVote, requestSent,
                    voteReceived, broadcastSent,
                    decisionC, coordinatorAlive >>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordinatorAlive
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, sentVote, requestSent,
                    voteReceived, broadcastSent,
                    decisionC, coordinatorAlive >>

DecideOnBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcastSent[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = broadcastSent[p]]
    /\ UNCHANGED << vote, alive, sentVote, requestSent,
                    voteReceived, broadcastSent,
                    decisionC, coordinatorAlive >>

DieParticipant(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << vote, decision, sentVote, requestSent,
                    voteReceived, broadcastSent,
                    decisionC, coordinatorAlive >>

ParticipantActions ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideOnBroadcast(p)
    \/ \E p \in participants : DieParticipant(p)

\*=====================================================================
\* Next-state relation
\*=====================================================================
Next ==
    \/ CoordinatorActions
    \/ ParticipantActions

\*=====================================================================
\* Specification
\*=====================================================================
Spec == Init /\ [][Next]_<<vote, alive, decision, sentVote,
                         requestSent, voteReceived,
                         broadcastSent, decisionC,
                         coordinatorAlive>>

\*=====================================================================
\* Type invariant (required by the configuration)
\*=====================================================================
TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ requestSent \in [participants -> BOOLEAN]
    /\ voteReceived \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \in [participants -> {commit, abort, notsent}]
    /\ decisionC \in {undecided, commit, abort}
    /\ coordinatorAlive \in BOOLEAN

====
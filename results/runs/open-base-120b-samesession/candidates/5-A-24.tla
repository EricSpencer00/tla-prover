---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    vote,                 \* [p \in participants -> {yes,no}]
    sentVote,             \* [p \in participants -> BOOLEAN]
    request,              \* [p \in participants -> BOOLEAN]   \* coordinator sent vote request
    voteRec,              \* [p \in participants -> {yes,no,waiting}]
    decisionSent,         \* [p \in participants -> {commit,abort,notsent}]
    participantDecision, \* [p \in participants -> {undecided,commit,abort}]
    participantAlive,    \* [p \in participants -> BOOLEAN]
    coordinatorAlive,    \* BOOLEAN
    coordinatorDecision  \* {undecided,commit,abort}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Vars == << vote, sentVote, request, voteRec, decisionSent,
           participantDecision, participantAlive,
           coordinatorAlive, coordinatorDecision >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ vote \in [participants -> {yes,no}]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ request = [p \in participants |-> FALSE]
    /\ voteRec = [p \in participants |-> waiting]
    /\ decisionSent = [p \in participants |-> notsent]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ coordinatorAlive = TRUE
    /\ coordinatorDecision = undecided

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordinatorSendReq ==
    \E p \in participants :
        /\ coordinatorAlive
        /\ ~request[p]
        /\ request' = [request EXCEPT ![p] = TRUE]
        /\ UNCHANGED << vote, sentVote, voteRec, decisionSent,
                         participantDecision, participantAlive,
                         coordinatorDecision, coordinatorAlive >>

CoordinatorReceiveVote ==
    \E p \in participants :
        /\ coordinatorAlive
        /\ coordinatorDecision = undecided
        /\ request[p]               \* vote request was sent
        /\ voteRec[p] = waiting
        /\ sentVote[p]              \* participant has sent its vote
        /\ voteRec' = [voteRec EXCEPT ![p] = vote[p]]
        /\ UNCHANGED << vote, sentVote, request, decisionSent,
                         participantDecision, participantAlive,
                         coordinatorDecision, coordinatorAlive >>

CoordinatorDetectFault ==
    \E p \in participants :
        /\ coordinatorAlive
        /\ coordinatorDecision = undecided
        /\ request[p] = TRUE
        /\ voteRec[p] = waiting
        /\ participantAlive[p] = FALSE
        /\ coordinatorDecision' = abort
        /\ UNCHANGED << vote, sentVote, request, voteRec,
                         decisionSent, participantDecision,
                         participantAlive, coordinatorAlive >>

CoordinatorMakeDecision ==
    /\ coordinatorAlive
    /\ coordinatorDecision = undecided
    /\ \A p \in participants : request[p] = TRUE
    /\ \A p \in participants : voteRec[p] # waiting
    /\ IF \A p \in participants : voteRec[p] = yes
          THEN coordinatorDecision' = commit
          ELSE coordinatorDecision' = abort
    /\ UNCHANGED << vote, sentVote, request, voteRec,
                     decisionSent, participantDecision,
                     participantAlive, coordinatorAlive >>

CoordinatorBroadcast ==
    \E p \in participants :
        /\ coordinatorAlive
        /\ coordinatorDecision # undecided
        /\ decisionSent[p] = notsent
        /\ decisionSent' = [decisionSent EXCEPT ![p] = coordinatorDecision]
        /\ UNCHANGED << vote, sentVote, request, voteRec,
                         participantDecision, participantAlive,
                         coordinatorDecision, coordinatorAlive >>

CoordinatorDie ==
    /\ coordinatorAlive
    /\ coordinatorAlive' = FALSE
    /\ UNCHANGED << vote, sentVote, request, voteRec,
                     decisionSent, participantDecision,
                     participantAlive, coordinatorDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantSendVote ==
    \E p \in participants :
        /\ participantAlive[p]
        /\ request[p]                \* vote request received
        /\ ~sentVote[p]
        /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
        /\ UNCHANGED << vote, request, voteRec, decisionSent,
                         participantDecision, participantAlive,
                         coordinatorDecision, coordinatorAlive >>

ParticipantAbortOnVote ==
    \E p \in participants :
        /\ participantAlive[p]
        /\ participantDecision[p] = undecided
        /\ sentVote[p] = TRUE
        /\ vote[p] = no
        /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
        /\ UNCHANGED << vote, sentVote, request, voteRec,
                         decisionSent, participantAlive,
                         coordinatorDecision, coordinatorAlive >>

ParticipantAbortOnTimeout ==
    \E p \in participants :
        /\ participantAlive[p]
        /\ participantDecision[p] = undecided
        /\ coordinatorAlive = FALSE
        /\ request[p] = FALSE          \* coordinator died before sending request
        /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
        /\ UNCHANGED << vote, sentVote, request, voteRec,
                         decisionSent, participantAlive,
                         coordinatorDecision, coordinatorAlive >>

ParticipantDecideOnBroadcast ==
    \E p \in participants :
        /\ participantAlive[p]
        /\ participantDecision[p] = undecided
        /\ decisionSent[p] # notsent
        /\ participantDecision' = [participantDecision EXCEPT ![p] = decisionSent[p]]
        /\ UNCHANGED << vote, sentVote, request, voteRec,
                         decisionSent, participantAlive,
                         coordinatorDecision, coordinatorAlive >>

ParticipantDie ==
    \E p \in participants :
        /\ participantAlive[p]
        /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
        /\ UNCHANGED << vote, sentVote, request, voteRec,
                         decisionSent, participantDecision,
                         coordinatorDecision, coordinatorAlive >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CoordinatorSendReq
    \/ CoordinatorReceiveVote
    \/ CoordinatorDetectFault
    \/ CoordinatorMakeDecision
    \/ CoordinatorBroadcast
    \/ CoordinatorDie
    \/ ParticipantSendVote
    \/ ParticipantAbortOnVote
    \/ ParticipantAbortOnTimeout
    \/ ParticipantDecideOnBroadcast
    \/ ParticipantDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ vote \in [participants -> {yes,no}]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ request \in [participants -> BOOLEAN]
    /\ voteRec \in [participants -> {yes,no,waiting}]
    /\ decisionSent \in [participants -> {commit,abort,notsent}]
    /\ participantDecision \in [participants -> {undecided,commit,abort}]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ coordinatorAlive \in BOOLEAN
    /\ coordinatorDecision \in {undecided,commit,abort}

====
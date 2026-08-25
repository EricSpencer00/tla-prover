---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
    coordAlive,
    coordFaulty,
    requestSent,
    coordDecision,
    coordBroadcast,
    voteSent,
    vote,
    preDecision,
    decision,
    forwardTable,
    participantsAlive,
    participantsFaulty

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty = ~coordAlive
    /\ requestSent \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordBroadcast \subseteq participants
    /\ voteSent \in [participants -> BOOLEAN]
    /\ vote \in [participants -> {yes, no}]
    /\ preDecision \in [participants -> {undecided, commit, abort}]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ forwardTable \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ participantsAlive \subseteq participants
    /\ participantsFaulty = participants \ participantsAlive

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ requestSent = FALSE
    /\ coordDecision = undecided
    /\ coordBroadcast = {}
    /\ voteSent = [p \in participants |-> FALSE]
    /\ vote = [p \in participants |-> yes]            \* will be set by SendVote
    /\ preDecision = [p \in participants |-> undecided]
    /\ decision = [p \in participants |-> undecided]
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]
    /\ participantsAlive = participants
    /\ participantsFaulty = {}

\* ----------------------------------------------------------------------
\* Helper for unchanged variables
\* ----------------------------------------------------------------------
UNCHANGED_VARS == <<coordAlive, coordFaulty, requestSent, coordDecision,
                    coordBroadcast, voteSent, vote, preDecision, decision,
                    forwardTable, participantsAlive, participantsFaulty>>

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendRequest ==
    /\ coordAlive
    /\ ~requestSent
    /\ requestSent' = TRUE
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                   voteSent, vote, preDecision, decision, forwardTable,
                   participantsAlive, participantsFaulty>>

CoordDecide ==
    /\ coordAlive
    /\ requestSent
    /\ \A p \in participants: voteSent[p]                 \* all votes have been sent
    /\ IF \E p \in participants: vote[p] = no
          THEN coordDecision' = abort
          ELSE coordDecision' = commit
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordBroadcast,
                   voteSent, vote, preDecision, decision, forwardTable,
                   participantsAlive, participantsFaulty>>

CoordBroadcastOne ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ p \in participants
    /\ coordBroadcast' = coordBroadcast \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                   voteSent, vote, preDecision, decision, forwardTable,
                   participantsAlive, participantsFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<requestSent, coordDecision, coordBroadcast,
                   voteSent, vote, preDecision, decision, forwardTable,
                   participantsAlive, participantsFaulty>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote ==
    \E p \in participantsAlive :
        /\ ~voteSent[p]
        /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
        /\ vote' = [vote EXCEPT ![p] = CHOOSE v \in {yes, no} : TRUE]
        /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                       coordBroadcast, preDecision, decision, forwardTable,
                       participantsAlive, participantsFaulty>>

PreDecideFromCoordinator ==
    \E p \in participantsAlive :
        /\ preDecision[p] = undecided
        /\ p \in coordBroadcast
        /\ coordDecision # undecided
        /\ preDecision' = [preDecision EXCEPT ![p] = coordDecision]
        /\ forwardTable' = [forwardTable EXCEPT ![p][p] = coordDecision]
        /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                       coordBroadcast, voteSent, vote, decision,
                       participantsAlive, participantsFaulty>>

PreDecideFromForward ==
    \E p \in participantsAlive :
        /\ preDecision[p] = undecided
        /\ \E q \in participants :
              /\ q # p
              /\ forwardTable[q][p] \in {commit, abort}
        LET d == IF \E q \in participants : q # p /\ forwardTable[q][p] = commit
                THEN commit ELSE abort IN
        /\ preDecision' = [preDecision EXCEPT ![p] = d]
        /\ forwardTable' = [forwardTable EXCEPT ![p][p] = d]
        /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                       coordBroadcast, voteSent, vote, decision,
                       participantsAlive, participantsFaulty>>

Forward ==
    \E p, q \in participants :
        /\ p \in participantsAlive
        /\ preDecision[p] # undecided
        /\ forwardTable[p][q] = notsent
        /\ forwardTable' = [forwardTable EXCEPT ![p][q] = preDecision[p]]
        /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                       coordBroadcast, voteSent, vote, preDecision, decision,
                       participantsAlive, participantsFaulty>>

Decide ==
    \E p \in participantsAlive :
        /\ decision[p] = undecided
        /\ preDecision[p] # undecided
        /\ \A q \in participants : forwardTable[p][q] # notsent
        /\ decision' = [decision EXCEPT ![p] = preDecision[p]]
        /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                       coordBroadcast, voteSent, vote, preDecision,
                       forwardTable, participantsAlive, participantsFaulty>>

AbortTimeout ==
    \E p \in participantsAlive :
        /\ decision[p] = undecided
        /\ coordAlive = FALSE
        /\ \A q \in participants : p \notin coordBroadcast
        /\ \A q \in participantsFaulty :
               \A r \in participantsAlive : forwardTable[q][r] = notsent
        /\ decision' = [decision EXCEPT ![p] = abort]
        /\ preDecision' = [preDecision EXCEPT ![p] = abort]
        /\ forwardTable' = [forwardTable EXCEPT ![p][p] = abort]
        /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                       coordBroadcast, voteSent, vote,
                       participantsAlive, participantsFaulty>>

Die ==
    \E p \in participantsAlive :
        /\ participantsAlive' = participantsAlive \ {p}
        /\ participantsFaulty' = participantsFaulty \cup {p}
        /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                       coordBroadcast, voteSent, vote, preDecision,
                       decision, forwardTable>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CoordSendRequest
    \/ CoordDecide
    \/ CoordBroadcastOne
    \/ CoordDie
    \/ SendVote
    \/ PreDecideFromCoordinator
    \/ PreDecideFromForward
    \/ Forward
    \/ Decide
    \/ AbortTimeout
    \/ Die

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, requestSent, coordDecision,
                     coordBroadcast, voteSent, vote, preDecision, decision,
                     forwardTable, participantsAlive, participantsFaulty>>

====
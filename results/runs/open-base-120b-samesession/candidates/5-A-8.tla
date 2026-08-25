---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    participants,   \* set of participant identifiers
    yes, no,         \* vote values
    undecided, commit, abort,   \* decision values
    waiting, notsent          \* auxiliary values for communication

VARIABLES
    cAlive,                \* coordinator alive flag
    coordDecision,         \* coordinator's decision (undecided/commit/abort)
    voteRequestSent,       \* [p \in participants |-> BOOLEAN] – request already sent?
    votesReceived,         \* [p \in participants |-> yes \/ no \/ waiting] – vote or waiting
    decisionSent,          \* [p \in participants |-> commit \/ abort \/ notsent] – broadcast status
    pAlive,                \* [p \in participants |-> BOOLEAN] – participant alive flag
    pVote,                 \* [p \in participants |-> yes \/ no] – participant's vote
    pSentVote,             \* [p \in participants |-> BOOLEAN] – has participant sent its vote?
    pDecision              \* [p \in participants |-> commit \/ abort \/ undecided] – final decision

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ cAlive = TRUE
    /\ coordDecision = undecided
    /\ voteRequestSent = [p \in participants |-> FALSE]
    /\ votesReceived = [p \in participants |-> waiting]
    /\ decisionSent = [p \in participants |-> notsent]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pVote \in [participants -> (yes \/ no)]   \* nondeterministic vote assignment
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\*  Coordinator actions
\* ----------------------------------------------------------------------
SendVoteRequest ==
    \E p \in participants :
        /\ cAlive
        /\ ~voteRequestSent[p]
        /\ UNCHANGED << coordDecision, votesReceived, decisionSent,
                       pAlive, pVote, pSentVote, pDecision >>
        /\ voteRequestSent' = [voteRequestSent EXCEPT ![p] = TRUE]

ReceiveVote ==
    \E p \in participants :
        /\ cAlive
        /\ coordDecision = undecided
        /\ voteRequestSent[p]            \* request has been sent
        /\ votesReceived[p] = waiting
        /\ pAlive[p]
        /\ pSentVote[p]
        /\ UNCHANGED << cAlive, coordDecision, voteRequestSent,
                       decisionSent, pAlive, pVote, pSentVote, pDecision >>
        /\ votesReceived' = [votesReceived EXCEPT ![p] = pVote[p]]

DetectFault ==
    \E p \in participants :
        /\ cAlive
        /\ coordDecision = undecided
        /\ voteRequestSent[p]
        /\ votesReceived[p] = waiting
        /\ ~pAlive[p]            \* participant crashed before sending vote
        /\ UNCHANGED << coordDecision, voteRequestSent,
                       votesReceived, decisionSent,
                       pAlive, pVote, pSentVote, pDecision >>
        /\ coordDecision' = abort

MakeDecision ==
    /\ cAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : votesReceived[p] # waiting
    /\ LET allYes == \A p \in participants : votesReceived[p] = yes
       IN coordDecision' = IF allYes THEN commit ELSE abort
    /\ UNCHANGED << cAlive, voteRequestSent, votesReceived,
                    decisionSent, pAlive, pVote, pSentVote, pDecision >>

BroadcastDecision ==
    \E p \in participants :
        /\ cAlive
        /\ coordDecision \in {commit, abort}
        /\ decisionSent[p] = notsent
        /\ UNCHANGED << cAlive, coordDecision, voteRequestSent,
                       votesReceived, pAlive, pVote, pSentVote, pDecision >>
        /\ decisionSent' = [decisionSent EXCEPT ![p] = coordDecision]

CoordDie ==
    /\ cAlive
    /\ UNCHANGED << coordDecision, voteRequestSent, votesReceived,
                   decisionSent, pAlive, pVote, pSentVote, pDecision >>
    /\ cAlive' = FALSE

\* ----------------------------------------------------------------------
\*  Participant actions
\* ----------------------------------------------------------------------
SendVote ==
    \E p \in participants :
        /\ pAlive[p]
        /\ voteRequestSent[p]
        /\ ~pSentVote[p]
        /\ UNCHANGED << cAlive, coordDecision, voteRequestSent,
                       votesReceived, decisionSent,
                       pAlive, pVote, pDecision >>
        /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]

AbortOnVote ==
    \E p \in participants :
        /\ pAlive[p]
        /\ pDecision[p] = undecided
        /\ pSentVote[p]
        /\ pVote[p] = no
        /\ UNCHANGED << cAlive, coordDecision, voteRequestSent,
                       votesReceived, decisionSent,
                       pAlive, pVote, pSentVote >>
        /\ pDecision' = [pDecision EXCEPT ![p] = abort]

AbortOnTimeout ==
    \E p \in participants :
        /\ pAlive[p]
        /\ pDecision[p] = undecided
        /\ ~cAlive                \* coordinator has died
        /\ ~voteRequestSent[p]    \* no request was ever sent
        /\ UNCHANGED << cAlive, coordDecision, voteRequestSent,
                       votesReceived, decisionSent,
                       pAlive, pVote, pSentVote >>
        /\ pDecision' = [pDecision EXCEPT ![p] = abort]

DecideOnBroadcast ==
    \E p \in participants :
        /\ pAlive[p]
        /\ pDecision[p] = undecided
        /\ decisionSent[p] # notsent
        /\ UNCHANGED << cAlive, coordDecision, voteRequestSent,
                       votesReceived, pAlive, pVote, pSentVote >>
        /\ pDecision' = [pDecision EXCEPT ![p] = decisionSent[p]]

PartDie ==
    \E p \in participants :
        /\ pAlive[p]
        /\ UNCHANGED << cAlive, coordDecision, voteRequestSent,
                       votesReceived, decisionSent,
                       pVote, pSentVote, pDecision >>
        /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]

\* ----------------------------------------------------------------------
\*  Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ SendVoteRequest
    \/ ReceiveVote
    \/ DetectFault
    \/ MakeDecision
    \/ BroadcastDecision
    \/ CoordDie
    \/ SendVote
    \/ AbortOnVote
    \/ AbortOnTimeout
    \/ DecideOnBroadcast
    \/ PartDie

\* ----------------------------------------------------------------------
\*  Fairness assumptions (weak fairness on progress actions only)
\* ----------------------------------------------------------------------
CoordProgress == 
    \/ SendVoteRequest
    \/ ReceiveVote
    \/ DetectFault
    \/ MakeDecision
    \/ BroadcastDecision

PartProgress ==
    \/ SendVote
    \/ AbortOnVote
    \/ AbortOnTimeout
    \/ DecideOnBroadcast

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< cAlive, coordDecision, voteRequestSent,
                        votesReceived, decisionSent,
                        pAlive, pVote, pSentVote, pDecision >>
                /\ WF_vars(CoordProgress)
                /\ WF_vars(PartProgress)

\* ----------------------------------------------------------------------
\*  Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ cAlive \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ voteRequestSent \in [participants -> BOOLEAN]
    /\ votesReceived \in [participants -> (yes \/ no \/ waiting)]
    /\ decisionSent \in [participants -> (commit \/ abort \/ notsent)]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> (yes \/ no)]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> (commit \/ abort \/ undecided)]

====
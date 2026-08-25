---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    coordAlive,          \* TRUE if coordinator is alive
    coordFaulty,         \* TRUE if coordinator has crashed
    coordDecision,       \* one of {undecided, commit, abort}
    requestSent,         \* [participants -> BOOLEAN], request sent to each participant?
    voteReceived,        \* [participants -> {yes,no,waiting}]
    broadcastSent,       \* [participants -> {commit,abort,notsent}]
    pAlive,              \* [participants -> BOOLEAN]
    pFaulty,             \* [participants -> BOOLEAN]
    pVote,               \* [participants -> {yes,no}]
    pSentVote,           \* [participants -> BOOLEAN]
    pDecision            \* [participants -> {undecided, commit, abort}]

\* ----------------------------------------------------------------------
\* Helper definitions
AllRequested == \A q \in participants: requestSent[q]
AllVotesReceived == \A q \in participants: voteReceived[q] # waiting
AllYes == \A q \in participants: voteReceived[q] = yes

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ requestSent = [p \in participants |-> FALSE]
    /\ voteReceived = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> notsent]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pVote = [p \in participants |-> CHOOSE v \in {yes,no}: TRUE]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
SendReq(p) ==
    /\ coordAlive
    /\ ~requestSent[p]
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordFaulty, coordDecision, voteReceived,
                    broadcastSent, pAlive, pFaulty, pVote,
                    pSentVote, pDecision>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ AllRequested
    /\ voteReceived[p] = waiting
    /\ pSentVote[p] = TRUE
    /\ voteReceived' = [voteReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent,
                    broadcastSent, pAlive, pFaulty, pVote,
                    pSentVote, pDecision>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ AllRequested
    /\ voteReceived[p] = waiting
    /\ pAlive[p] = FALSE
    /\ pSentVote[p] = FALSE
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent,
                    voteReceived, broadcastSent,
                    pAlive, pFaulty, pVote,
                    pSentVote, pDecision>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ AllRequested
    /\ AllVotesReceived
    /\ coordDecision' = IF AllYes THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent,
                    voteReceived, broadcastSent,
                    pAlive, pFaulty, pVote,
                    pSentVote, pDecision>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    requestSent, voteReceived,
                    pAlive, pFaulty, pVote,
                    pSentVote, pDecision>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, requestSent, voteReceived,
                    broadcastSent, pAlive, pFaulty,
                    pVote, pSentVote, pDecision>>

\* ----------------------------------------------------------------------
\* Participant actions
SendVote(p) ==
    /\ pAlive[p]
    /\ requestSent[p]            \* has received a request
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    requestSent, voteReceived, broadcastSent,
                    pAlive, pFaulty, pVote, pDecision>>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    requestSent, voteReceived, broadcastSent,
                    pAlive, pFaulty, pVote, pSentVote>>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ requestSent[p] = FALSE
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    requestSent, voteReceived, broadcastSent,
                    pAlive, pFaulty, pVote, pSentVote>>

DecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ broadcastSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = broadcastSent[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    requestSent, voteReceived, broadcastSent,
                    pAlive, pFaulty, pVote, pSentVote>>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    requestSent, voteReceived, broadcastSent,
                    pVote, pSentVote, pDecision>>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ \E p \in participants: SendReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideOnBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Variables tuple for actions
vars == <<coordAlive, coordFaulty, coordDecision, requestSent,
          voteReceived, broadcastSent, pAlive, pFaulty,
          pVote, pSentVote, pDecision>>

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ requestSent \in [participants -> BOOLEAN]
    /\ voteReceived \in [participants -> ({yes, no} \cup {waiting})]
    /\ broadcastSent \in [participants -> ({commit, abort} \cup {notsent})]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> {yes, no}]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]

====
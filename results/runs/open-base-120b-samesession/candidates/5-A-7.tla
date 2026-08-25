---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    coordAlive, coordFaulty, coordDecision,
    coordReqSent, coordVotes, coordBroadcast,
    pAlive, pFaulty, pVote, pSentVote, pDecision, pReqReceived

\*=====================================================================
\*  Variable collections
\*=====================================================================
vars == << 
    coordAlive, coordFaulty, coordDecision,
    coordReqSent, coordVotes, coordBroadcast,
    pAlive, pFaulty, pVote, pSentVote, pDecision, pReqReceived
>>

\*=====================================================================
\*  Type invariant
\*=====================================================================
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordReqSent \in [participants -> BOOLEAN]
    /\ coordVotes   \in [participants -> {yes, no, waiting}]
    /\ coordBroadcast \in [participants -> {commit, abort, notsent}]
    /\ pAlive    \in [participants -> BOOLEAN]
    /\ pFaulty   \in [participants -> BOOLEAN]
    /\ pVote     \in [participants -> {yes, no}]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pReqReceived \in [participants -> BOOLEAN]

\*=====================================================================
\*  Initial state
\*=====================================================================
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordReqSent = [i \in participants |-> FALSE]
    /\ coordVotes   = [i \in participants |-> waiting]
    /\ coordBroadcast = [i \in participants |-> notsent]
    /\ pAlive    = [i \in participants |-> TRUE]
    /\ pFaulty   = [i \in participants |-> FALSE]
    /\ pVote     \in [participants -> {yes, no}]
    /\ pSentVote = [i \in participants |-> FALSE]
    /\ pDecision = [i \in participants |-> undecided]
    /\ pReqReceived = [i \in participants |-> FALSE]

\*=====================================================================
\*  Coordinator actions
\*=====================================================================
SendReq(p) ==
    /\ p \in participants
    /\ coordAlive
    /\ ~coordReqSent[p]
    /\ coordReqSent' = [coordReqSent EXCEPT ![p] = TRUE]
    /\ pReqReceived' = [pReqReceived EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordVotes, coordBroadcast,
                    pAlive, pFaulty, pVote, pSentVote, pDecision >>

ReceiveVote(p) ==
    /\ p \in participants
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordReqSent[p]
    /\ coordVotes[p] = waiting
    /\ pSentVote[p]
    /\ coordVotes' = [coordVotes EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordBroadcast,
                    pAlive, pFaulty, pVote, pSentVote, pDecision,
                    pReqReceived >>

DetectFault(p) ==
    /\ p \in participants
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordReqSent[p]
    /\ coordVotes[p] = waiting
    /\ ~pAlive[p]
    /\ ~pSentVote[p]
    /\ coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordReqSent,
                    coordVotes, coordBroadcast,
                    pAlive, pFaulty, pVote, pSentVote, pDecision,
                    pReqReceived >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordVotes[p] # waiting
    /\ coordDecision' = IF \A p \in participants : coordVotes[p] = yes
                         THEN commit
                         ELSE abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordReqSent,
                    coordVotes, coordBroadcast,
                    pAlive, pFaulty, pVote, pSentVote, pDecision,
                    pReqReceived >>

Broadcast(p) ==
    /\ p \in participants
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordBroadcast[p] = notsent
    /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordVotes,
                    pAlive, pFaulty, pVote, pSentVote, pDecision,
                    pReqReceived >>

DieCoord ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordDecision, coordReqSent, coordVotes,
                    coordBroadcast,
                    pAlive, pFaulty, pVote, pSentVote, pDecision,
                    pReqReceived >>

\*=====================================================================
\*  Participant actions
\*=====================================================================
SendVote(p) ==
    /\ p \in participants
    /\ pAlive[p]
    /\ pReqReceived[p]
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordVotes, coordBroadcast,
                    pAlive, pFaulty, pVote, pDecision,
                    pReqReceived >>

AbortOnVote(p) ==
    /\ p \in participants
    /\ pAlive[p]
    /\ pSentVote[p]
    /\ pDecision[p] = undecided
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordVotes, coordBroadcast,
                    pAlive, pFaulty, pVote, pSentVote,
                    pReqReceived >>

AbortOnTimeout(p) ==
    /\ p \in participants
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ coordFaulty
    /\ ~pReqReceived[p]
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordVotes, coordBroadcast,
                    pAlive, pFaulty, pVote, pSentVote,
                    pReqReceived >>

DecideFromBroadcast(p) ==
    /\ p \in participants
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ coordBroadcast[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = coordBroadcast[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordVotes, coordBroadcast,
                    pAlive, pFaulty, pVote, pSentVote,
                    pReqReceived >>

DieParticipant(p) ==
    /\ p \in participants
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << coordAlive, coordFaulty, coordDecision,
                    coordReqSent, coordVotes, coordBroadcast,
                    pVote, pSentVote, pDecision,
                    pReqReceived >>

\*=====================================================================
\*  Next-state relation
\*=====================================================================
Next ==
    \/ \E p \in participants: SendReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ DieCoord
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: DieParticipant(p)

\*=====================================================================
\*  Specification
\*=====================================================================
Spec == Init /\ [][Next]_vars

\*=====================================================================
\*  Invariant
\*=====================================================================
INVARIANT TypeInv

====
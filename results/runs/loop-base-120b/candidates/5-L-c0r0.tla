---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    pVote,          \* [participants -> {yes,no}]
    pAlive,         \* [participants -> BOOLEAN]
    pDecision,      \* [participants -> {undecided,commit,abort}]
    pSent,          \* SUBSET participants
    requestSent,    \* SUBSET participants
    votesReceived,  \* [participants -> {yes,no,waiting}]
    broadcastSent,  \* [participants -> {commit,abort,notsent}]
    coordAlive,     \* BOOLEAN
    coordDecision   \* {undecided,commit,abort}

vars == << pVote, pAlive, pDecision, pSent, requestSent,
           votesReceived, broadcastSent, coordAlive, coordDecision >>

\*=====================================================================
\* Type invariant
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSent \subseteq participants
    /\ requestSent \subseteq participants
    /\ votesReceived \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \in [participants -> {commit, abort, notsent}]
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}

\*=====================================================================
\* Initial state
Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSent = {}
    /\ requestSent = {}
    /\ votesReceived = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> notsent]
    /\ coordAlive = TRUE
    /\ coordDecision = undecided

\*=====================================================================
\* Coordinator actions
SendVoteReq(p) ==
    /\ coordAlive
    /\ p \notin requestSent
    /\ requestSent' = requestSent \cup {p}
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                    votesReceived, broadcastSent, coordAlive, coordDecision >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in requestSent
    /\ votesReceived[p] = waiting
    /\ p \in pSent
    /\ votesReceived' = [votesReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                    requestSent, broadcastSent, coordAlive, coordDecision >>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in requestSent
    /\ votesReceived[p] = waiting
    /\ pAlive[p] = FALSE
    /\ p \notin pSent
    /\ coordDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                    requestSent, votesReceived, broadcastSent, coordAlive >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ requestSent = participants
    /\ \A q \in participants: votesReceived[q] # waiting
    /\ IF \A q \in participants: votesReceived[q] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                    requestSent, votesReceived, broadcastSent, coordAlive >>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                    requestSent, votesReceived, coordDecision, coordAlive >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent,
                    requestSent, votesReceived, broadcastSent, coordDecision >>

\*=====================================================================
\* Participant actions
SendVote(p) ==
    /\ pAlive[p] = TRUE
    /\ p \in requestSent
    /\ p \notin pSent
    /\ pSent' = pSent \cup {p}
    /\ UNCHANGED << pVote, pAlive, pDecision,
                    requestSent, votesReceived, broadcastSent,
                    coordAlive, coordDecision >>

AbortOnVote(p) ==
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ p \in pSent
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pSent,
                    requestSent, votesReceived, broadcastSent,
                    coordAlive, coordDecision >>

AbortOnTimeout(p) ==
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ p \notin requestSent
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pSent,
                    requestSent, votesReceived, broadcastSent,
                    coordAlive, coordDecision >>

DecideFromBroadcast(p) ==
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ broadcastSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = broadcastSent[p]]
    /\ UNCHANGED << pVote, pAlive, pSent,
                    requestSent, votesReceived, broadcastSent,
                    coordAlive, coordDecision >>

ParticipantDie(p) ==
    /\ pAlive[p] = TRUE
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << pVote, pDecision, pSent,
                    requestSent, votesReceived, broadcastSent,
                    coordAlive, coordDecision >>

\*=====================================================================
\* Next-state relation
Next ==
    \/ \E p \in participants: SendVoteReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)

\*=====================================================================
\* Fairness assumptions (weak fairness on progress actions, not on death)
Fairness ==
    /\ \A p \in participants: WF_vars( SendVoteReq(p) )
    /\ \A p \in participants: WF_vars( ReceiveVote(p) )
    /\ \A p \in participants: WF_vars( DetectFault(p) )
    /\ WF_vars( MakeDecision )
    /\ \A p \in participants: WF_vars( Broadcast(p) )
    /\ \A p \in participants: WF_vars( SendVote(p) )
    /\ \A p \in participants: WF_vars( AbortOnVote(p) )
    /\ \A p \in participants: WF_vars( AbortOnTimeout(p) )
    /\ \A p \in participants: WF_vars( DecideFromBroadcast(p) )

\*=====================================================================
\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\*=====================================================================
\* Invariant required by the configuration
INVARIANT TypeInv

====
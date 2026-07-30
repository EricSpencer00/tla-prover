---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding status at each participant's forwarding table entry, per participant
\* index: notsent (no pre-decision yet), commit, or abort.
\* The table lives at each participant, and the entry at its own index is the
\* pre-decision it received from either the coordinator or a peer.
STATUS == {notsent, commit, abort}

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, pFwd, coordReq, coordVote,
          coordBroadcast, coordDecision, coordAlive, coordFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent, pFwd, coordReq,
           coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* The base ACP-SB safety and progress properties apply unchanged.
TypeInvNB ==
    /\ pVote \in [participants -> {yes, no, undecided}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> {waiting, commit, abort}]
    /\ pFwd \in [participants -> [participants -> STATUS]]
    /\ coordReq \in {undecided, wait}
    /\ coordVote \in {undecided, wait}
    /\ coordBroadcast \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {notsent, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ pVote = [p \in participants |-> undecided]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSent = [p \in participants |-> waiting]
    /\ pFwd = [p \in participants |-> [q \in participants |-> notsent]]
    /\ coordReq = undecided
    /\ coordVote = undecided
    /\ coordBroadcast = [p \in participants |-> notsent]
    /\ coordDecision = notsent
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

Ac1 == ~ \E p \in participants : pDecision[p] = commit /\ \E p \in participants : pDecision[p] = abort

Ac2 == (\E p \in participants : pDecision[p] = commit) => (\A p \in participants : pVote[p] = yes)

\* Abort covers both one participant voting no and any participant crashing.
Ac3 == (\E p \in participants : pDecision[p] = abort) =>
       (\E p \in participants : pVote[p] = no \/ pFaulty[p] \/ coordFaulty)

Ac4 == \A p \in participants : (pDecision[p] = undecided) ~> (pDecision[p] # undecided)

Ac5 == \A p \in participants : pAlive[p] => (pDecision[p] = undecided) ~> (pDecision[p] # undecided)

\* A participant must forward its pre-decision to everyone else before finalizing;
\* that is what stops it from being stuck forever when the coordinator crashes.
Ac5Prime == \A p \in participants :
    (pAlive[p] /\ pDecision[p] = undecided) ~>
        (pDecision[p] = commit \/ pDecision[p] = abort)

InitNB == Init

\* Coordinator sends the request to vote.
RequestCoord ==
    /\ coordAlive
    /\ coordReq = undecided
    /\ coordReq' = wait
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, pFwd, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant sends its vote to the coordinator.
Vote ==
    /\ \E p \in participants :
         /\ pAlive[p]
         /\ pVote[p] = undecided
         /\ \E v \in {yes, no} : pVote' = [pVote EXCEPT ![p] = v]
    /\ UNCHANGED <<pAlive, pDecision, pFaulty, pSent, pFwd, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* The coordinator collects votes and decides commit or abort.
DecideCoord ==
    /\ coordAlive
    /\ coordReq = wait
    /\ coordVote = undecided
    /\ coordVote' = wait
    /\ coordDecision' = IF \A p \in participants : pVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, pFwd, coordReq,
                   coordBroadcast, coordAlive, coordFaulty>>

\* Broadcast the coordinator's decision to a participant who has not been sent to.
BroadcastCoord ==
    /\ coordAlive
    /\ coordDecision # notsent
    /\ \E p \in participants :
         /\ coordBroadcast[p] = notsent
         /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, pFwd, coordReq,
                   coordVote, coordDecision, coordAlive, coordFaulty>>

\* A participant receives a pre-decision from the coordinator.
PreDecideFromCoord ==
    /\ \E p \in participants :
         /\ pAlive[p]
         /\ pFwd[p][p] = notsent
         /\ coordBroadcast[p] # notsent
         /\ pFwd' = [pFwd EXCEPT ![p][p] = coordBroadcast[p]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant receives a pre-decision forwarded by another participant.
PreDecideFromPeer ==
    /\ \E p, q \in participants :
         /\ pAlive[p]
         /\ pFwd[p][p] = notsent
         /\ pFwd[q][p] # notsent
         /\ pFwd' = [pFwd EXCEPT ![p][p] = pFwd[q][p]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant forwards its pre-decision to another participant.
Forward ==
    /\ \E p, q \in participants :
         /\ pAlive[p]
         /\ pFwd[p][p] # notsent
         /\ pFwd[p][q] = notsent
         /\ q # p
         /\ pFwd' = [pFwd EXCEPT ![p][q] = pFwd[p][p]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* Once a participant has forwarded its pre-decision to all others, it finalizes.
DecideParticipant ==
    /\ \E p \in participants :
         /\ pAlive[p]
         /\ pDecision[p] = undecided
         /\ \A q \in participants : pFwd[p][q] # notsent
         /\ pDecision' = [pDecision EXCEPT ![p] = pFwd[p][p]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, pFwd, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant aborts on timeout when the coordinator has died and no one can
\* provide the decision via broadcast or forwarding.
AbortOnTimeout ==
    /\ \E p \in participants :
         /\ pAlive[p]
         /\ pDecision[p] = undecided
         /\ ~coordAlive
         /\ \A q \in participants : coordBroadcast[q] = notsent
         /\ \A q \in participants : pAlive[q] => \A r \in participants : pFwd[q][r] = notsent
         /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, pFwd, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

DetectCoordFault ==
    /\ coordAlive
    /\ coordFaulty' = TRUE
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, pFwd, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordFaulty>>

\* A participant crashes (becomes faulty), excluding the decision it already
\* finalized.  The forwarding table is never cleared on a crash.
Die ==
    /\ \E p \in participants :
         /\ pAlive[p]
         /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
         /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecision, pSent, pFwd, coordReq,
                   coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

NextNB ==
    \/ RequestCoord \/ Vote \/ DecideCoord \/ BroadcastCoord
    \/ PreDecideFromCoord \/ PreDecideFromPeer \/ Forward \/ DecideParticipant
    \/ AbortOnTimeout \/ DetectCoordFault \/ Die

SpecNB ==
    /\ InitNB
    /\ [][NextNB]_vars
    /\ WF_vars(PreDecideFromCoord)
    /\ WF_vars(PreDecideFromPeer)
    /\ WF_vars(Forward)
    /\ WF_vars(DecideParticipant)
    /\ WF_vars(Vote)
    /\ WF_vars(DecideCoord)
    /\ WF_vars(BroadcastCoord)
    /\ WF_vars(Die)

Properties == Ac1 /\ Ac2 /\ Ac3 /\ Ac4 /\ Ac5Prime

====
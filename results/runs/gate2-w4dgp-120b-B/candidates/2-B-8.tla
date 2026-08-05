---- MODULE ACP_NB ------------------------------------------------
EXTENDS ACP_SB

\* The non blocking broadcast now forwards every received predecision
\* to all other participants BEFORE it is locally applied.  Participants
\* keep a "forward" map, and a participant "decides" only after its own
\* predecision has been forwarded to all others; if a participant's own
\* predecision were not yet forwarded it could be silently lost and the
\* protocol would no longer be non blocking.  The change therefore adds
\* the forward table and two guarded actions (forward, preDecideOnForward)
\* that together preserve the intended commit/abort agreement.
\* NOTE: All other actions, properties, and comments are unchanged.

TypeInvParticipantNB == participant \in [
    participants -> [
        vote      : {yes, no},
        alive     : BOOLEAN,
        decision  : {undecided, commit, abort},
        faulty    : BOOLEAN,
        voteSent  : BOOLEAN,
        forward   : [ participants -> {notsent, commit, abort} ]
    ]
]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

InitParticipantNB == participant \in [
    participants -> [
        vote     : {yes, no},
        alive    : {TRUE},
        decision : {undecided},
        faulty   : {FALSE},
        voteSent : {FALSE},
        forward  : [ participants -> {notsent} ]
    ]
]

InitNB == InitParticipantNB /\ InitCoordinator

\* forward(i,j): participant i forwards its already received predecision to j
\*   (i never forwards to itself; i's own predecision is forwarded to j,
\*    not delivered to i).
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = [
                        @ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]
                    ]]
                /\ UNCHANGED<<coordinator>>

\* preDecideOnForward(i,j): participant i receives a predecision from j
\*   (delivered after j has actually forwarded it).
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = [
                                @ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]
                            ]]
                           \/ UNCHANGED<<coordinator>>

\* preDecide(i): participant i receives decision directly from the coordinator
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = [
                     @ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]
                 ]]
                /\ UNCHANGED<<coordinator>>

\* decideNB(i): a participant may finally decide only after forwarding
\*   its predecision to every other participant.
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = [
                    @ EXCEPT !.decision = participant[i].forward[i]
                ]]
               /\ UNCHANGED<<coordinator>>

abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED<<coordinator>>

parProgNB(i,j) == \/ sendVote(i)
                  \/ abortOnVote(i)
                  \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j)
                  \/ preDecideOnForward(i,j)
                  \/ abortOnTimeout(i)
                  \/ preDecide(i)
                  \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants :
                    WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)
AllAbort  == \A i \in participants : <>(participant[i].decision = abort  \/ participant[i].faulty)
AllCommitYesVotes == \A i \in participants :
                        \A j \in participants : participant[j].vote = yes
                    ~>  participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
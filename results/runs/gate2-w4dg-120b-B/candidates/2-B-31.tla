---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB).
\* AC5: Non blocking via a reliable broadcast: a participant forwards a
\* broadcast message to all participants before delivering it locally, so
\* no correct participant is starved.  Since a participant does not forward
\* to itself, its own predecision is stored in forward[i] before it is
\* delivered locally.
\* LIVENESS PROPERTY: Any undecided participant eventually receives a decision
\* (commit or abort), i.e. is never starved by the broadcast.

EXTENDS ACP_SB

\* Participant record gains a "forward" variable to hold the forwarded decision.
\* Coordinator record is unchanged.
TypeInvParticipantNB == participant \in [
  participants -> [
    vote     : {yes, no},
    alive    : BOOLEAN,
    decision : {undecided, commit, abort},
    faulty   : BOOLEAN,
    voteSent : BOOLEAN,
    forward  : [ participants -> {notsent, commit, abort} ]
  ]
]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

InitParticipantNB == \E r \in participant :
  participant = [i \in participants |-> [
    vote     |-> r[i].vote,
    alive    |-> r[i].alive,
    decision |-> r[i].decision,
    faulty   |-> r[i].faulty,
    voteSent |-> r[i].voteSent,
    forward  |-> (p \in participants |-> notsent)
  ]]

InitNB == InitParticipantNB /\ InitCoordinator

\* forward(i,j): participant i sends its predecision to participant j.
\* Coordinator's broadcast is owned by i, so participant i only forwards what
\* it has already received from the coordinator.
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward[j] = participant[i].forward[i]]]
                /\ UNCHANGED coordinator

\* preDecideOnForward(i,j): participant i receives the decision forwarded by
\* participant j and stores it in its own forward[i] (predecision).
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward[i] = participant[j].forward[i]]]
                           /\ UNCHANGED coordinator

\* preDecide(i): participant i receives the coordinator's broadcast directly.
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward[i] = coordinator.broadcast[i]]]
                /\ UNCHANGED coordinator

\* decideNB(i): the actual decision; requires i's predecision to have been
\* forwarded to all other participants, which is the non blocking condition.
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]]
               /\ UNCHANGED coordinator

\* abortOnTimeout(i): simulated timeout if the coordinator has died and no
\* further broadcast can reach an alive participant.
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j, k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED coordinator

\* Non-blocking pairwise interleaving: each pair (i,j) may be the active
\* participant or the active participant's forwardee.  Coordinator actions
\* interleave with participant actions.
parProgNB(i,j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) \/ preDecideOnForward(i,j) \/ preDecide(i)
                  \/ decideNB(i) \/ abortOnTimeout(i)

parProgNNB == \E i, j \in participants : parDie(i) \/ parProgNB(i,j)
progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* Every undecided participant is eventually delivered a decision (commit or
\* abort) -- this is what rules out starvation by the broadcast.
NoStarvation == \A i \in participants : (participant[i].decision = undecided) ~> (participant[i].decision # undecided)

====
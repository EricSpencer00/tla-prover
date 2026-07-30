---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>
\* Non blocking Atomic Committment Protocol (ACP-NB) with a reliable broadcast.
\* Upon reception a broadcast message is forwarded to all participants before
\* being delivered locally; participant i does not forward to itself, so forward
\* records the decision before it's delivered.  The change fixes a TLC error:
\* preDecideOnForward now updates the whole participant record, not just the
\* forwarding slot, so the next-state relation keeps the record completely
\* specified and the model checker does not flag an incompletely specified
\* successor state.
EXTENDS ACP_SB

--------------------------------------------------------------------------------
\* Participants now carry a "forward" slot recording the decision received
\* (or not received) from each other participant.

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

--------------------------------------------------------------------------------
InitParticipantNB == participant \in [
  participants -> [
    vote     : {yes, no},
    alive    : TRUE,
    decision : undecided,
    faulty   : FALSE,
    voteSent : FALSE,
    forward  : [ participants -> {notsent} ]
  ]
]

InitNB == InitParticipantNB /\ InitCoordinator

--------------------------------------------------------------------------------
\* Participant statements: forward(i,j) and preDecideOnForward(i,j) are
\* the ones that realize the reliable broadcast.

\* forward(i,j): participant i forwards its predecision to participant j.
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = [
                    @ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]
                  ]]
                /\ UNCHANGED coordinator

\* preDecideOnForward(i,j): participant i receives a decision from j.
\* The corrected version updates the whole participant record, not just
\* the forward slot, so the next-state relation stays fully specified.
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = [
                               @ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]
                             ]]
                           /\ UNCHANGED coordinator

\* preDecide(i): participant i receives the coordinator's decision.
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = [
                    @ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]
                  ]]
                /\ UNCHANGED coordinator

\* decideNB(i): after all forwards are in, participant i decides locally.
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = [
                   @ EXCEPT !.decision = participant[i].forward[i]
                 ]]
               /\ UNCHANGED coordinator

\* abortOnTimeout(i): simulated timeout under a dead coordinator.
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants :
                          participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants :
                          ~participant[j].alive /\ participant[k].alive =>
                            participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [
                         @ EXCEPT !.decision = abort
                       ]]
                     /\ UNCHANGED coordinator

--------------------------------------------------------------------------------
parProgNB(i,j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) \/ preDecideOnForward(i,j)
                  \/ abortOnTimeout(i) \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)
progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants :
                WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

--------------------------------------------------------------------------------
\* (SOME) INVALID PROPERTIES: these are not part of the corrected model,
\* they illustrate the danger the protocol guards against.
AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)
AllAbort == \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)
AllCommitYesVotes == \A i \in participants :
  \A j \in participants : participant[j].vote = yes
    ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
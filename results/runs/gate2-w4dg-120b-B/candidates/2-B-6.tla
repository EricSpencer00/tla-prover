---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>
\* Non blocking Atomic Committment Protocol (ACP-NB).  The non blocking
\* property is achieved by a reliable broadcast: upon reception a broadcast
\* message is forwarded to all participants before it is delivered locally,
\* which is modelled by each participant's "forward" map.
EXTENDS ACP_SB

\* Participants now carry a "forward" map.  Coordinator is unchanged.
TypeInvParticipantNB ==
  participant \in [
    participants -> [
      vote     : {yes, no},
      alive    : BOOLEAN,
      decision : {undecided, commit, abort},
      faulty   : BOOLEAN,
      voteSent : BOOLEAN,
      forward  : [participants -> {notsent, commit, abort}]
    ]
  ]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

\* Initially participants have not forwarded anything.
InitParticipantNB ==
  participant \in [
    participants -> [
      vote     : {yes, no},
      alive    : TRUE,
      decision : undecided,
      faulty   : FALSE,
      voteSent : FALSE,
      forward  : [participants -> notsent]
    ]
  ]

InitNB == InitParticipantNB /\ InitCoordinator

\* Forwarding of a predecision from participant i to participant j.
\* i forwards only if alive and it has already received an incoming decision.
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i] =
        [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
  /\ UNCHANGED <<coordinator>>

\* A participant receives a decision that another participant has forwarded.
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT ![i] =
        [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
  /\ UNCHANGED <<coordinator>>

\* A participant receives the coordinator's decision.
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] =
        [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
  /\ UNCHANGED <<coordinator>>

\* After a participant has forwarded its predecision to everyone, it decides.
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]]
  /\ UNCHANGED <<coordinator>>

\* A timeout forces an abort if the coordinator never decides.
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED <<coordinator>>

\* Non-blocking protocol interleaving (the sendVote / abortOnVote etc. are SB
\* actions, forwarded unchanged here).
parProgNB(i, j) ==
  \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
  \/ forward(i, j) \/ preDecideOnForward(i, j) \/ abortOnTimeout(i)
  \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i, j \in participants : parDie(i) \/ parProgNB(i, j)

progNNB == parProgNNB \/ coordProgN

fairnessNB ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i, j))
  /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* (SOME) INVALID PROPERTIES in the original version:
AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)
AllAbort  == \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)
AllCommitYesVotes ==
  \A i \in participants : \A j \in participants : participant[j].vote = yes ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
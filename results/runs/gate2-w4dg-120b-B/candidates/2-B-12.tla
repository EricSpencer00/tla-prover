---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB).
\* A participant forwards a predecision to each other participant before
\* acting on it, and only forwards after it has decided (locally) itself.
\* This "forward-then-deliver" discipline is what makes the broadcast
\* reliable even though a participant never forwards to itself.

EXTENDS ACP_SB

\* Every participant now carries a "forward" map: for each participant j it
\* records what decision it has forwarded to j (or notsent).  The coordinator
\* is unchanged.

TypeInvParticipantNB ==
  participant \in [
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

\* Initially nothing has been forwarded.

InitParticipantNB ==
  participant \in [
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

\* A live participant i who has already decided forwards its decision to a
\* live participant j that has not yet received it.
\* This action never changes anybody's locally stored decision.
forward(i,j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
  /\ UNCHANGED coordinator

\* Participant i receives (the predecision from) participant j.
\* This is the delivery half: i copies the decision j previously forwarded.
preDecideOnForward(i,j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
  /\ UNCHANGED coordinator

\* Participant i receives (the predecision from) the coordinator.
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
  /\ UNCHANGED coordinator

\* A live participant i that has already predecided decides for real, but only
\* once it has forwarded that predecision to every other participant.
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]]
  /\ UNCHANGED coordinator

\* If the coordinator has crashed before completing the broadcast, and no
\* live participant has a predecision to forward, i times out and aborts.
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

\* The rest of the protocol is unchanged from ACP_SB.

parProgNB(i,j) ==
  \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
  \/ forward(i,j) \/ preDecideOnForward(i,j) \/ abortOnTimeout(i)
  \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
  /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* (SOME) INVALID PROPERTIES: a property that is not true and not needed.

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)
AllAbort  == \A i \in participants : <>(participant[i].decision = abort  \/ participant[i].faulty)

====
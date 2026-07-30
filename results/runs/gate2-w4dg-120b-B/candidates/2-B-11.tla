---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>
\* Non blocking Atomic Committment Protocol (ACP-NB).  The non blocking
\* property AC5 is obtained by a reliable broadcast: a participant forwards the
\* decision it received to all other participants, and then delivers it locally.
\* The forward-then-deliver order is what made the next-state relation under-
\* specified in the original listing.
EXTENDS ACP_SB

\* The participant record is extended with a "forward" variable.  The
\* coordinator record is unchanged from ACP_SB.
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

\* Initially, participants have not forwarded anything yet.
InitParticipantNB ==
  participant \in [
    participants -> [
      vote     : {yes, no},
      alive    : {TRUE},
      decision : {undecided},
      faulty   : {FALSE},
      voteSent : {FALSE},
      forward  : [participants -> {notsent}]
    ]
  ]

InitNB == InitParticipantNB /\ InitCoordinator

\* forward(i,j): participant i forwards its predecision to participant j.
\* Participant i does not forward to itself, so forward[i] is where the local
\* decision is stored before it is delivered.
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
  /\ UNCHANGED <<coordinator>>

\* preDecideOnForward(i,j): participant i receives the decision forwarded by j.
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
  /\ UNCHANGED <<coordinator>>

\* preDecide(i): participant i receives the decision from the coordinator.
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
  /\ UNCHANGED <<coordinator>>

\* decideNB(i): a participant decides only after it has forwarded its (pre)decision
\* to all other participants.
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]]
  /\ UNCHANGED <<coordinator>>

\* abortOnTimeout(i): the timeout case is simulated by explicit conditions.
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED <<coordinator>>

\* The rest of the actions (sendVote, abortOnVote, abortOnTimeoutRequest,
\* preDecide, decideSB, parDie, coordProgB) are unchanged from ACP_SB.
parProgNB(i, j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                   \/ forward(i, j) \/ preDecideOnForward(i, j) \/ abortOnTimeout(i)
                   \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i, j \in participants : parDie(i) \/ parProgNB(i, j)

progNNB == parProgNNB \/ coordProgN

fairnessNB ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i, j))
  /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* (SOME) INVALID PROPERTIES: deliberately left unchanged.
AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)
AllAbort  == \A i \in participants : <>(participant[i].decision = abort  \/ participant[i].faulty)
AllCommitYesVotes ==
  \A i \in participants : \A j \in participants : participant[j].vote = yes ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
---- MODULE ACP_NB ----
\* Non blocking Atomic Commit in a system with a reliable broadcast. The
\* broadcast is realized by having each participant forward the coordinator's
\* decision to every other alive participant; a participant can only decide
\* once its own forwarded decision has reached all other participants. A
\* participant's own forwarded message is stored in forward[i][i] and does
\* not need to be sent over the network (the coordinator's decision is not
\* broadcast to the coordinator itself).
\* A participant's decision is only ever recorded on its own forward[i][i],
\* never by copying another participant's forward entry -- that is what
\* prevents a silent participant from "adopting" a different participant's
\* decision.

EXTENDS ACP_SB

\* Participant type extended with a forward table; coordinator unchanged
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

\* Initially nothing has been forwarded by any participant
InitParticipantNB ==
  participant \in [
    participants -> [
      vote      : {yes, no},
      alive     : {TRUE},
      decision  : {undecided},
      faulty    : {FALSE},
      voteSent  : {FALSE},
      forward   : [participants -> {notsent}]
    ]
  ]

InitNB == InitParticipantNB /\ InitCoordinator

\* forward(i,j): participant i sends its own predecision to participant j
\* (i # j, i is alive, it has a predecision, it has not sent it to j yet)
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
  /\ UNCHANGED <<coordinator>>

\* preDecideOnForward(i,j): participant i receives the forwarded predecision
\* from participant j (i # j)
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
  /\ UNCHANGED <<coordinator>>

\* preDecide(i): participant i receives the coordinator's broadcasted decision
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
  /\ UNCHANGED <<coordinator>>

\* decideNB(i): once participant i's own predecision has been sent to every
\* other participant, it records its final decision
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]]
  /\ UNCHANGED <<coordinator>>

\* abortOnTimeout(i): simulated timeout when the coordinator has died before
\* deciding and no live participant has yet received a forwarded decision
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED <<coordinator>>

\* Participant actions, parameterized over both i and j (for forwarding)
parProgNB(i, j) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ forward(i, j)
  \/ preDecideOnForward(i, j)
  \/ abortOnTimeout(i)
  \/ preDecide(i)
  \/ decideNB(i)

\* Bounded concurrency: any participant may die, and at most one action interleaves
parProgNNB == \E i, j \in participants : parDie(i) \/ parProgNB(i, j)

progNNB == parProgNNB \/ coordProgN

fairnessNB ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i, j))
  /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* (SOME) invalid properties from the original spec, retained unchanged here

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort == \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
  \A j \in participants : participant[j].vote = yes
    ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
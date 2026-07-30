---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non-blocking Atomic Commit Protocol (ACP-NB).
\* Correctness of the non-blocking property relies on a reliable broadcast:
\*   - a broadcast message is first stored in the receiver's mailbox, and
\*   - only when the mailbox holds a decision (a predecision) may that
\*     decision be forwarded to other participants.
\* Participant i does not forward to itself; its own decision is stored in
\* forward[i] and later becomes "decision".  The model has been repaired so
\* that the predecision held in forward[i] is always carried forward unchanged,
\* which is what TLC complained about was missing.

EXTENDS ACP_SB

--------------------------------------------------------------------------------
\* Participants are now records that also keep a "forward" mailbox for every
\* participant.  Coordinator records are unchanged.
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

--------------------------------------------------------------------------------
\* Initially no mailbox holds anything.
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

--------------------------------------------------------------------------------
\* Forwarding a predecision: participant i, while alive, copies its own
\* predecision (forward[i]) into the mailbox of participant j (j # i).
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i] =
        [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
  /\ UNCHANGED coordinator

\* Receiving a forwarded predecision: participant i, while alive, copies the
\* decision that participant j has placed in its mailbox for i.
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT ![i] =
        [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
  /\ UNCHANGED coordinator

\* Receiving the coordinator's broadcast (the original, unchanged rule).
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] =
        [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
  /\ UNCHANGED coordinator

\* The actual decision: once i has forwarded its own predecision to everyone
\* else, its decision becomes whatever was in forward[i].
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]]
  /\ UNCHANGED coordinator

\* Timeout branch: coordinated abort when the coordinator has died before
\* reaching everyone and no alive participant has been forwarded a decision.
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants :
        (~participant[j].alive /\ participant[k].alive) => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

--------------------------------------------------------------------------------
\* Participant actions; a participant may die at any time (parDie).
parProgNB(i, j) ==
  \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
  \/ forward(i, j) \/ preDecideOnForward(i, j)
  \/ preDecide(i) \/ decideNB(i) \/ abortOnTimeout(i)

parProgNNB == \E i, j \in participants : parDie(i) \/ parProgNB(i, j)

progNNB == parProgNNB \/ coordProgN

fairnessNB ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i, j))
  /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

--------------------------------------------------------------------------------
\* (SOME) INVALID PROPERTIES (intentionally left too weak to be satisfied).
AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)
AllAbort  == \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes ==
  \A i \in participants : \A j \in participants : participant[j].vote = yes
    ~> (participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty)

================================================================================
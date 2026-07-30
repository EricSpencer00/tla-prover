---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>
\* Non blocking Atomic Committment Protocol (ACP-NB)
\* This version adds a "forward" variable per participant and forwards a
\* participant's predecision to every other participant before the decision
\* itself is taken (the definition of "non blocking" here).  When a
\* predecision arrives from a participant, only that participant's local
\* "forward" record is updated; the decision field and everybody else's
\* forward records are untouched.  The invariants below are unchanged from
\* the original protocol and must still hold, so the fix here is a change
\* to the next-state relation, not a weakening of any property.

EXTENDS ACP_SB

--------------------------------------------------------------------------------
\* Participants: vote, alive, decision, faulty, voteSent, and the new forward.
\* Coordinator type unchanged.
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
\* Initially forward = notsent for every participant, for every destination.
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
\* forward(i,j): participant i forwards its predecision to participant j.
\* Only forward[i] is touched; decision and other forward entries stay.
forward(i,j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward =
                     [@ EXCEPT ![j] = participant[i].forward[i]]]]
  /\ UNCHANGED <<coordinator>>

\* preDecideOnForward(i,j): participant i receives the decision j forwarded.
\* Only forward[i] is set; decision is untouched until decideNB fires.
preDecideOnForward(i,j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward =
                     [@ EXCEPT ![i] = participant[j].forward[i]]]]
  /\ UNCHANGED <<coordinator>>

\* preDecide(i): participant i receives the coordinator's broadcast.
\* Same single-field update as above (forward[i] only).
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward =
                     [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
  /\ UNCHANGED <<coordinator>>

\* decideNB(i): the actual decision, after all forward records are in.
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision =
                     participant[i].forward[i]]]
  /\ UNCHANGED <<coordinator>>

\* abortOnTimeout(i): simulated timeout when coordinator and forwards die.
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED <<coordinator>>

---------------------------------------------------------------------------------
\* The interleaving is driven by two levels (coordProgN and parProgNB(i,j));
\* the fairness condition is what keeps it from stalling while the
\* coordinator is alive.
parProgNB(i,j) ==
  \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
  \/ forward(i,j) \/ preDecideOnForward(i,j) \/ abortOnTimeout(i)
  \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB ==
  /\ \A i \in participants :
       WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
  /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

--------------------------------------------------------------------------------
\* These properties are unchanged from the original protocol (they were
\* flagged invalid, not missing) and must still hold here.
AllCommit ==
  \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort ==
  \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes ==
  \A i \in participants :
    \A j \in participants : participant[j].vote = yes ~>
      (participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty)

====
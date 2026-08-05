---- MODULE ACP_NB -------------------------------------------------------------
\* Non blocking Atomic Committment Protocol; extension of ACP_SB.  The non-blocking
\* property AC5 is realized by a reliable broadcast: a message is forwarded to all
\* participants before it is delivered locally, and a participant's own
\* predecision is stored in participant[i].forward[i] (so it need not forward to
\* itself).
\* This module was repaired so that its successor function is total (no variable
\* left unassigned by an action) and so that its original safety properties hold.
EXTENDS ACP_SB

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

\* forward(i,j): participant i relays its predecision to participant j.
\* preDecideOnForward(i,j): participant i receives the forwarded predecision from j.
\* decideNB(i): the commit/abort action, now named to avoid a clash with ACP_SB's
\* already-defined decide(i) action.

forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] =
                     [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
                /\ UNCHANGED <<coordinator>>

preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] =
                                [@ EXCEPT !.forward =
                                    [@ EXCEPT ![i] = participant[j].forward[i]]]]
                           /\ UNCHANGED <<coordinator>>

preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] =
                     [@ EXCEPT !.forward =
                        [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
                /\ UNCHANGED <<coordinator>>

decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] =
                    [@ EXCEPT !.decision = participant[i].forward[i]]]
               /\ UNCHANGED <<coordinator>>

parProgNB(i,j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) \/ preDecideOnForward(i,j) \/ abortOnTimeout(i)
                  \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)
progNNB    == parProgNNB \/ coordProgN
fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* (SOME) INVALID PROPERTIES: left untouched here (they were not repaired)

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)
AllAbort  == \A i \in participants : <>(participant[i].decision = abort  \/ participant[i].faulty)
AllCommitYesVotes == \A i \in participants : \A j \in participants : participant[j].vote = yes
                     ~>  participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

================================================================================
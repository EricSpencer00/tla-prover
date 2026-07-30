---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB).  The non blocking property
\* AC5 is obtained by using a reliable broadcast: a participant forwards a
\* predecision to all other participants before it is delivered locally.  Since
\* participant i does not forward to itself, forward[i] records the decision
\* before it becomes the participant's own decision.

EXTENDS ACP_SB

--------------------------------------------------------------------------------

\* Participants now carry a "forward" map recording, for each peer, what decision
\* (if any) has been forwarded to it.  The coordinator definition is unchanged.
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

\* Initially nothing has been forwarded yet.
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
\* Only alive participants forward, and never to themselves.
forward(i,j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i] = [
        @ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]
      ]]
  /\ UNCHANGED coordinator

\* preDecideOnForward(i,j): participant i receives a forwarded predecision.
preDecideOnForward(i,j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [
        @ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]
      ]]
  /\ UNCHANGED coordinator

\* preDecide(i): participant i receives the coordinator's predecision.
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [
        @ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]
      ]]
  /\ UNCHANGED coordinator

\* decideNB(i): participant i decides, once it has forwarded its predecision
\* to everyone else (reliable broadcast completed).
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT ![i] = [
        @ EXCEPT !.decision = participant[i].forward[i]
      ]]
  /\ UNCHANGED coordinator

\* abortOnTimeout(i): simulated timeout when the coordinator and all dead
\* participants failed to deliver a predecision.
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j,k \in participants :
        ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

--------------------------------------------------------------------------------

\* SAFETY PROPERTY: every participant eventually commits or is known faulty.
AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

====
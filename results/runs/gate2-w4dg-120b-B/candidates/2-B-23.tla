---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Commit Protocol (ACP-NB).  The non blocking property AC5
\* is obtained by using a reliable broadcast: upon reception a broadcast
\* message is forwarded to all participants before being delivered locally.  Since
\* participant i does not forward to itself, forward[i] is used to store the
\* decision before it is delivered (becomes "decision").

EXTENDS ACP_SB

\* Participants: now carry a forward table recording the broadcast messages
\* this participant has already forwarded to each other participant.

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

\* Initially participants have not forwarded anything yet.

InitParticipantNB == participant \in [
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

\* Forwarding: an alive participant i forwards its predecision to participant
\* j (j # i) once it has received it.

forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = [
                     @ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]
                   ]]
                /\ UNCHANGED <<coordinator>>

\* A participant receives a forwarded decision from another participant.

preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = [
                                @ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]
                              ]]
                           \/ UNCHANGED <<coordinator>>

\* A participant receives the coordinator's decision (first hop, before any
\* forwarding).

preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = [
                     @ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]
                   ]]
                /\ UNCHANGED <<coordinator>>

\* Actual decision: once a participant i has forwarded its predecision to
\* every other participant, it decides in accordance with it.

decideNB(i) == /\ participant[i].alive
                /\ \A j \in participants : participant[i].forward[j] # notsent
                /\ participant' = [participant EXCEPT ![i] = [
                     @ EXCEPT !.decision = participant[i].forward[i]
                   ]]
                /\ UNCHANGED <<coordinator>>

\* A timeout (simulated: coordinator and all dead participants died silently
\* before forwarding) forces alive undecided participants to abort.

abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED <<coordinator>>

parProgNB(i,j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) \/ preDecideOnForward(i,j) \/ abortOnTimeout(i)
                  \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants :
                  WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
                /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* (Some) invalid properties that must not be weakened.

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                         \A j \in participants : participant[j].vote = yes
                     ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
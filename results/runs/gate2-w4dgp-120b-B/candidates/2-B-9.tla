---- MODULE ACP_NB -------------------------------------------------------------
\* Timestamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>
\* Non-blocking Atomic Commit Protocol (ACP-NB).  The non-blocking property AC5
\* is achieved by a reliable broadcast: a participant forwards its (pre)decision
\* to every other participant before delivering it locally, so a participant
\* never decides on a message that has not been confirmed by the whole group.
EXTENDS ACP_SB

\* Participants now carry "forward" to store the decision they have received
\* from each other participant (or from the coordinator).
TypeInvParticipantNB == participants \in [
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

InitParticipantNB == participants \in [
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

\* forward(i,j): participant i forwards its (pre)decision to participant j
\* (i must be alive, must already hold a decision for itself, and must not
\* have forwarded it to j before).  Each pair (i,j) is forwarded at most once,
\* and the action is an actual update of the participant record, never a
\* no-op assignment with participant' = participant.
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = [
                     @ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]
                   ]]
                /\ UNCHANGED <<coordinator>>

\* preDecideOnForward(i,j): participant i adopts the decision that participant
\* j has already forwarded to it (i must be alive and undecided).
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = [
                                @ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]
                              ]]
                           /\ UNCHANGED <<coordinator>>

\* preDecide(i): participant i adopts the decision broadcast by the coordinator.
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = [
                     @ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]
                   ]]
                /\ UNCHANGED <<coordinator>>

\* decideNB(i): once i has forwarded its own (pre)decision to every other
\* participant, it turns final -- this is the one irreversible action.
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = [
                    @ EXCEPT !.decision = participant[i].forward[i]
                  ]]
               /\ UNCHANGED <<coordinator>>

\* abortOnTimeout(i): when the coordinator has failed and no undecided
\* participant can receive a decision from either the coordinator or a peer,
\* the protocol aborts.
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j, k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED <<coordinator>>

\* FOR N PARTICIPANTS

parProgNB(i,j) == \/ sendVote(i)
                  \/ abortOnVote(i)
                  \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) \/ preDecideOnForward(i,j) \/ abortOnTimeout(i)
                  \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i, j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* (SOME) INVALID PROPERTIES

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                        \A j \in participants : participant[j].vote = yes
                     ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty
===============================================================================
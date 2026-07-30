---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB) extended with a reliable
\* broadcast: a participant forwards any decision it has (including its own
\* predecision) to every other participant before it is considered delivered.
\* The safety properties are unchanged; only the next-state relation is fixed.

EXTENDS ACP_SB

\* Participants now carry a "forward" dispatch table that records, per recipient,
\* the decision already forwarded to that participant.  The coordinator is
\* otherwise untouched from ACP_SB.

TypeInvParticipantNB == participant \in [
  participants -> [
    vote      : {yes, no},
    alive     : BOOLEAN,
    decision  : {undecided, commit, abort},
    faulty    : BOOLEAN,
    voteSent  : BOOLEAN,
    forward   : [ participants -> {notsent, commit, abort} ]
  ]
]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

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

\* Forwarding: participant i, still alive, forwards the decision it holds
\* (itself or one received) to participant j, which has not yet received it.
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = 
                     [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
                /\ UNCHANGED <<coordinator>>

\* Receiving a forwarded decision: participant i adopts the decision
\* forwarded to it by participant j.
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = 
                                [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
                           /\ UNCHANGED <<coordinator>>

\* Receiving the coordinator's broadcast: the participant's own (pre)decision
\* takes the coordinator's decision, again recorded in its forward table.
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = 
                     [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
                /\ UNCHANGED <<coordinator>>

\* A participant decides once it has forwarded its predecision to EVERYONE.
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]]
               /\ UNCHANGED <<coordinator>>

\* A timeout forces an abort when the coordinator is dead and no broadcast
\* or forwarding can possibly revive a lost participant's decision.
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED <<coordinator>>

\* Complete the round: every participant must eventually decide or abort, so
\* the coordinator propagates votes and the participants forward decisions.
parProg(i,j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                \/ forward(i,j) \/ preDecideOnForward(i,j) \/ abortOnTimeout(i)
                \/ preDecide(i) \/ decideNB(i)

parProgN == \E i,j \in participants : parDie(i) \/ parProg(i,j)

progN == parProgN \/ coordProgN

fairnessN == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProg(i,j))
             /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progN]_<<coordinator, participant>> /\ fairnessN

\* (SOME) INVALID PROPERTIES: retained from ACP_SB, unchanged here.

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort == \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                       \A j \in participants : participant[j].vote = yes
                     ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
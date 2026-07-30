---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB). The non blocking property AC5
\* is obtained by using a reliable broadcast: a participant forwards a deci-
\* sion it has received to every other participant before delivering it locally.
\* Since a participant does not forward to itself, its own decision is kept in
\* a per-participant "forward" entry.

EXTENDS ACP_SB

--------------------------------------------------------------------------------

\* The participant record keeps a "forward" entry for every participant, plus the
\* decision that has been forwarded to it (or notsent yet).
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

--------------------------------------------------------------------------------

\* Initially, participants have not forwarded anything.
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

--------------------------------------------------------------------------------

\* Forward: participant i forwards the decision it has predecided on to participant j.
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = [
                     @ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]
                   ]]
                /\ UNCHANGED <<coordinator>>

\* Receive a forwarded decision from participant j.
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = [
                                @ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]
                              ]]
                           /\ UNCHANGED <<coordinator>>

\* Receive the coordinator's broadcast directly.
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = [
                     @ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]
                   ]]
                /\ UNCHANGED <<coordinator>>

\* Decide once every participant has been forwarded this participant's predecision.
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = [
                    @ EXCEPT !.decision = participant[i].forward[i]
                  ]]
               /\ UNCHANGED <<coordinator>>

\* A timeout aborts a participant that is undecided while the coordinator has died.
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive
                          => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED <<coordinator>>

--------------------------------------------------------------------------------

\* The participant's own vote is sent to the coordinator, and an explicit abort
\* vote (or a timeout request) can trigger an abort.
parProgNB(i,j) == \/ sendVote(i)
                  \/ abortOnVote(i)
                  \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j)
                  \/ preDecideOnForward(i,j)
                  \/ abortOnTimeout(i)
                  \/ preDecide(i)
                  \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants :
                    WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

--------------------------------------------------------------------------------

\* (Discarded) Invalid claims: at most one participant votes no; a no vote means
\* abort; and the commit decision is never reached.
AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                         \A j \in participants : participant[j].vote = yes
                     ~>  participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
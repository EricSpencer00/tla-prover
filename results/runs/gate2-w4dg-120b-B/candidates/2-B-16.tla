---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>
\* Non blocking Atomic Commit Protocol (ACP_NB); the non blocking property AC5
\* is obtained by a reliable broadcast: upon reception a message is forwarded
\* to all participants before being delivered locally (so forward[i] holds the
\* decision before it becomes "decision")
EXTENDS ACP_SB

\* Every participant carries a "forward" array; coordinator is unchanged
TypeInvParticipantNB == participant \in [
  participants -> [ vote     : {yes, no}, alive : BOOLEAN,
                    decision : {undecided, commit, abort},
                    faulty   : BOOLEAN, voteSent : BOOLEAN,
                    forward  : [ participants -> {notsent, commit, abort} ] ] ]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

\* Initially nothing is forwarded
InitParticipantNB == participant \in [
  participants -> [ vote     |-> {yes, no}, alive |-> TRUE,
                    decision |-> undecided, faulty |-> FALSE,
                    voteSent |-> FALSE,
                    forward  |-> [ participants -> {notsent} ] ] ]

InitNB == InitParticipantNB /\ InitCoordinator

\* Forward(i,j): alive participant i forwards its predecision to participant j
\* (i does not forward to itself)
forward(i,j) == /\ i # j /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [ participant EXCEPT ![i] =
                     [ @ EXCEPT !.forward = [ @ EXCEPT ![j] = participant[i].forward[i] ] ] ]
                /\ UNCHANGED coordinator

\* preDecideOnForward(i,j): i receives participant j's forwarded decision
preDecideOnForward(i,j) == /\ i # j /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [ participant EXCEPT ![i] =
                                [ @ EXCEPT !.forward = [ @ EXCEPT ![i] = participant[j].forward[i] ] ] ]
                           /\ UNCHANGED coordinator

\* preDecide(i): i receives coordinator's decision
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [ participant EXCEPT ![i] =
                     [ @ EXCEPT !.forward = [ @ EXCEPT ![i] = coordinator.broadcast[i] ] ] ]
                /\ UNCHANGED coordinator

\* decideNB(i): after i has forwarded its (pre)decision to all participants
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [ participant EXCEPT ![i] = [ @ EXCEPT !.decision = participant[i].forward[i] ] ]
               /\ UNCHANGED coordinator

\* abortOnTimeout(i): participant i times out if coordinator is dead and no
\* decision has reached it (simulated condition)
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants :
                          (~participant[j].alive /\ participant[k].alive) => participant[j].forward[k] = notsent
                     /\ participant' = [ participant EXCEPT ![i] = [ @ EXCEPT !.decision = abort ] ]
                     /\ UNCHANGED coordinator

\* Non-blocking progress: every participant eventually gets its decision
parProgNB(i,j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) \/ preDecideOnForward(i,j) \/ abortOnTimeout(i)
                  \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)
progNNB    == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* (SOME) INVALID PROPERTIES: left as declared, not weakened
AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)
AllAbort  == \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)
AllCommitYesVotes == \A i \in participants :
  \A j \in participants : participant[j].vote = yes ~>
    (participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty)

====
---- MODULE ACP_NB -------------------------------------------------------------
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB)
\* The non blocking property AC5 is obtained by using a reliable broadcast 
\* implemented as follows:
\*   - upon reception of a broadcast message, this message is forwarded to all
\*     participants before it's delivered to the local site;
\*   - since participant i does not forward to itself, forward[i] is used to 
\*     store the decision before it's delivered (and becomes "decision")

EXTENDS ACP_SB

--------------------------------------------------------------------------------

\* Participants type is extended with a "forward" variable.  Coordinator type unchanged.
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

--------------------------------------------------------------------------------

\* Initially, participants have not forwarded anything yet
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

\* Forwarding: participant i forwards its predecision to participant j
\*   IF i is alive, i's decision is known (in forward[i]), and i hasn't forwarded to j
\*   THEN forward[i][j] := forward[i][i]
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] =
                     [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]
                   ]
                /\ UNCHANGED<<coordinator>>

\* Receiving a forwarded decision (a predecision)
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] =
                                [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]
                              ]
                           \/ UNCHANGED<<coordinator>>

\* Receiving the coordinator's decision (a predecision)
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] =
                     [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]
                   ]
                /\ UNCHANGED<<coordinator>>

\* Actual decision, once the predecision has been forwarded to everybody
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] =
                    [@ EXCEPT !.decision = participant[i].forward[i]]]
               /\ UNCHANGED<<coordinator>>

\* Abort on timeout (simulated, not based on real time)
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants :
                           ~participant[j].alive /\ participant[k].alive
                           => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] =
                          [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED<<coordinator>>

--------------------------------------------------------------------------------

\* The combined participant program (non-blocking version)
parProgNB(i,j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) \/ preDecideOnForward(i,j) \/ abortOnTimeout(i)
                  \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

--------------------------------------------------------------------------------

\* (SOME) INVARIANT TESTS (intentionally left suspect)

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                         \A j \in participants : participant[j].vote = yes
                     ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

================================================================================
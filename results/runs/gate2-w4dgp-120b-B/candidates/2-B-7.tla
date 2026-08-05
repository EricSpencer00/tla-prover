---- MODULE ACP_NB
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

\* Participants type is extended with a "forward" variable.  Coordinator type is unchanged.

TypeInvParticipantNB  == participant \in  [
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

\* Particpant statements that realize a better broadcast 

\* forward(i,j): forwarding of the predecision from participant i to participant j
\* i forwards its decision to j only if i is alive and i has a decision saved in its own forward[i]
\* and has not yet forwarded that decision to j
\* (this avoids a participant being stuck waiting for a forward from a dead or slow participant)

forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = 
                     [@ EXCEPT !.forward = 
                       [@ EXCEPT ![j] = participant[i].forward[i]]
                     ]
                   ]
                /\ UNCHANGED<<coordinator>>


\* preDecideOnForward(i,j): participant i receives decision from participant j
\* i predecides only when i is alive, has no predecision yet, and receives one from j
\* (j's broadcast to i may have arrived before i's broadcast to j)

preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = 
                                [@ EXCEPT !.forward = 
                                  [@ EXCEPT ![i] = participant[j].forward[i]]
                                ]
                              ]
                           \/ UNCHANGED<<coordinator>>


\* preDecide(i): participant i receives decision from coordinator
\* i predecides only when i is alive, has no predecision yet, and receives one from coordinator

preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = 
                     [@ EXCEPT !.forward =
                       [@ EXCEPT ![i] = coordinator.broadcast[i]]
                     ]
                   ]
                /\ UNCHANGED<<coordinator>>


\* decideNB(i): participant i decides, once it has a locally saved predecision and 
\* has forwarded that predecision to every other participant
\* (the condition on forwarded decisions matters only for the duration of the broadcast)

decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = 
                    [@ EXCEPT !.decision = participant[i].forward[i]]
                  ]
               /\ UNCHANGED<<coordinator>>


\* abortOnTimeout(i): the coordinator has died before anybody could decide; the
\* abort is only possible when the coordinator's death is reliably observable

abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED<<coordinator>>

---------------------------------------------------------------------------------

\* FOR N PARTICIPANTS (the dead participant in the root state never receives or forwards)

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

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

--------------------------------------------------------------------------------

\* (SOME) INVALID PROPERTIES for the buggy protocol (not to be fixed)

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <>(participant[i].decision = abort  \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                         \A j \in participants : participant[j].vote = yes
                     ~>  participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

================================================================================
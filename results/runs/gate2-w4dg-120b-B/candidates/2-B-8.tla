---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB)
\* The non blocking property AC5 is obtained by using a reliable broadcast 
\* implemented as follows:
\*   - upon reception of a broadcast message this message is forwarded to all
\*     participants before it's delivered to the local site;
\*   - since participant i does not forward to itself, forward[i] is used to
\*     store the decision before it's delivered (and becomes "decision")

EXTENDS ACP_SB

\* Participants now carry a "forward" variable; coordinator is unchanged.

TypeInvParticipantNB  == participant \in [
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

\* forward(i,j): participant i forwards its predecision to participant j
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

\* preDecideOnForward(i,j): participant i receives decision via forward from j
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

\* preDecide(i): participant i receives decision broadcast from coordinator
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] =
                     [@ EXCEPT !.forward =
                       [@ EXCEPT ![i] = coordinator.broadcast[i]]
                     ]
                   ]
                /\ UNCHANGED<<coordinator>>

\* decideNB(i): participant i decides once its predecision has been forwarded
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] =
                    [@ EXCEPT !.decision = participant[i].forward[i]]
                  ]
               /\ UNCHANGED<<coordinator>>

\* abortOnTimeout(i): if the coordinator is dead and no decision is forthcoming
\* from either coordinator or a dead participant, decide abort
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED<<coordinator>>

\* For N participants the actions are interleaved with coordinator actions
parProgNB(i,j) == \/ sendVote(i) 
                  \/ abortOnVote(i)
                  \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) 
                  \/ preDecideOnForward(i,j) 
                  \/ preDecide(i) 
                  \/ decideNB(i) 
                  \/ abortOnTimeout(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants :
                 WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* A valid ACID property: every committed participant must have voted yes
AllCommitYesVotes == \A i \in participants :
                         (\E j \in participants :
                          participant[j].decision = commit)
                     ~>
                         (\E j \in participants :
                          participant[j].decision = commit \/ participant[j].faulty)

====
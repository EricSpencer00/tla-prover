---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB)
\* The non blocking property AC5 is obtained by using a reliable broadcast 
\* implemented as follows:
\*   - upon reception of a broadcast message, this message is forwarded to all
\*     participants before it's delivered to the local site;
\*   - since participant i does not forward to itself, forward[i] is used to 
\*     store the decision before it's delivered (and becomes "decision")

EXTENDS ACP_SB

\*---------------------------------------------------------------------*
\* Types
\*---------------------------------------------------------------------*

\* Participants type is extended with a "forward" variable.  
\* Coordinator type is unchanged.
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

\*---------------------------------------------------------------------*
\* Initial state
\*---------------------------------------------------------------------*
InitParticipantNB == participant \in [
                       participants -> [
                         vote      : {yes, no},
                         alive     : TRUE,
                         decision  : undecided,
                         faulty    : FALSE,
                         voteSent  : FALSE,
                         forward   : [ participants -> notsent ]
                       ]
                     ]

InitNB == InitParticipantNB /\ InitCoordinator

\*---------------------------------------------------------------------*
\* Participant actions that realize a better broadcast 
\*---------------------------------------------------------------------*

\* forward(i,j): forwarding of the predecision from participant i to participant j
\* Preconditions:
\*   - i and j are distinct
\*   - i is alive
\*   - i has already a predecision stored in forward[i]
\*   - i has not yet forwarded this decision to j
\* Effect:
\*   - participant i records its decision for j in forward[j]
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
\* Preconditions:
\*   - i and j are distinct
\*   - i is alive and has not yet received any decision
\*   - j has already forwarded its decision to i
\* Effect:
\*   - i stores the received decision as its own predecision (forward[i])
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = 
                                [@ EXCEPT !.forward = 
                                  [@ EXCEPT ![i] = participant[j].forward[i]]
                                ]
                              ]
                           /\ UNCHANGED<<coordinator>>

\* preDecide(i): participant i receives decision from coordinator
\* Preconditions:
\*   - i is alive and has not yet received any decision
\*   - coordinator has sent a decision to i
\* Effect:
\*   - i stores the coordinator's decision as its own predecision
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = 
                     [@ EXCEPT !.forward =
                       [@ EXCEPT ![i] = coordinator.broadcast[i]]
                     ]
                   ]
                /\ UNCHANGED<<coordinator>>

\* decideNB(i): Actual decision, after predecision has been forwarded
\* Preconditions:
\*   - i is alive
\*   - i has forwarded its predecision to all other participants
\* Effect:
\*   - i's final decision becomes the predecision stored in forward[i]
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = 
                    [@ EXCEPT !.decision = participant[i].forward[i]]
                  ]
               /\ UNCHANGED<<coordinator>>

\* abortOnTimeout(i): conditions for a timeout are simulated
\* Preconditions:
\*   - i is alive and still undecided
\*   - the coordinator is dead
\*   - every alive participant has not yet received a decision from the coordinator
\*   - every dead participant has not forwarded any decision to any alive participant
\* Effect:
\*   - i decides abort
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j, k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED<<coordinator>>

\*---------------------------------------------------------------------*
\* Combined participant program (for a given i and j)
\*---------------------------------------------------------------------*
parProgNB(i,j) == \/ sendVote(i) 
                  \/ abortOnVote(i)
                  \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) 
                  \/ preDecideOnForward(i,j) 
                  \/ abortOnTimeout(i) 
                  \/ preDecide(i) 
                  \/ decideNB(i)

\*---------------------------------------------------------------------*
\* Overall system program
\*---------------------------------------------------------------------*
parProgNNB == \E i, j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\*---------------------------------------------------------------------*
\* (SOME) INVALID PROPERTIES 
\*---------------------------------------------------------------------*
AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <>(participant[i].decision = abort  \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                         \A j \in participants : participant[j].vote = yes
                     ~>  participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

=============================================================================
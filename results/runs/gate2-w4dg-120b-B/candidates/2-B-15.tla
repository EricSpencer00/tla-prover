---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>
\* Non blocking Atomic Commit Protocol with a reliable broadcast.  A
\* broadcast decision is first stored in the sender's "forward" record and
\* then delivered to every other participant; a participant may decide once
\* its own forward entry has been sent to (or received from) all others.
\* The artifact fixed here is the next-state relation of preDecideOnForward:
\* it failed to preserve the coordinator state, so this state was dropped
\* from the successor and TLC complained the state was incomplete.

EXTENDS ACP_SB

--------------------------------------------------------------------------------

\* Participants now carry a "forward" record of the decision they are
\* propagating; the coordinator is unchanged.

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

\* Initial state: forward records are empty.

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

\* A non-faulty participant forwards its predecision to another participant.

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

\* A participant adopts the predecision it receives from another participant.
\* This clause is the one that used to drop the coordinator from the successor,
\* which is what TLC complained about; now coordinator is untouched.

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

\* Participant i receives the decision broadcast from the coordinator.
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = 
                     [@ EXCEPT !.forward = 
                       [@ EXCEPT ![i] = coordinator.broadcast[i]]
                     ]
                   ]
                /\ UNCHANGED<<coordinator>>

\* A participant decides once it has sent its predecision to everyone.
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = 
                    [@ EXCEPT !.decision = participant[i].forward[i]]
                  ]
               /\ UNCHANGED<<coordinator>>

\* Simulated timeout: an undecided participant aborts when the coordinator
\* and all (potentially dead) participants have failed to deliver.
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED<<coordinator>>

\* Progress: votes, abort on vote, timeout request, plus the new forward/predecide.

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

\* (Invalid but retained as per the brief: these are not true properties.)

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)
AllAbort  == \A i \in participants : <>(participant[i].decision = abort  \/ participant[i].faulty)
AllCommitYesVotes == \A i \in participants :
                         \A j \in participants : participant[j].vote = yes
                     ~>  participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
---- MODULE ACP_NB -------------------------------------------------
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Commit Protocol (ACP-NB), an extension of ACP_SB
\* that implements the coordinator's broadcast as an explicit reliable
\* message passing primitive: each participant forwards the decision it
\* received to every other participant before its own decision is
\* committed (so a lost broadcast message cannot leave one participant
\* behind).  The type invariant and the initial state are extended with
\* the fresh "forward" variable; all other modules (ACP_SB and the
\* properties below) are unchanged.

EXTENDS ACP_SB

\* Participants now have a "forward" table recording, for each participant
\* in the system, the decision that participant forwarded to this one.
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

\* Initially no decision has been forwarded anywhere.
InitParticipantNB == participant \in [
                       participants -> [
                         vote      : {yes, no},
                         alive     : {TRUE},
                         decision  : {undecided},
                         faulty    : {FALSE},
                         voteSent  : {FALSE},
                         forward   : [ participants -> {notsent} ]
                       ]
                     ]

InitNB == InitParticipantNB /\ InitCoordinator

--------------------------------------------------------------------------------
\* A participant forwards its received decision to another participant.
\* participant i's own forward[i] slot is the decision it (pre)decided on;
\* the other slots are all messages i has forwarded out.
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [ participant EXCEPT ![i] =
                     [ @ EXCEPT !.forward = [ @ EXCEPT ![j] = participant[i].forward[i] ] ]
                   ]
                /\ UNCHANGED <<coordinator>>

\* A participant adopts the decision it receives from another participant.
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [ participant EXCEPT ![i] =
                                 [ @ EXCEPT !.forward =
                                      [ @ EXCEPT ![i] = participant[j].forward[i] ] ]
                               ]
                           /\ UNCHANGED <<coordinator>>

\* A participant adopts the decision it receives from the coordinator (the
\* first delivery mechanism before any forwarding happens).
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [ participant EXCEPT ![i] =
                     [ @ EXCEPT !.forward =
                          [ @ EXCEPT ![i] = coordinator.broadcast[i] ] ]
                   ]
                /\ UNCHANGED <<coordinator>>

\* The actual decision is made once the participant has collected a
\* forwarded decision from every other participant (including its own).
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [ participant EXCEPT ![i] =
                    [ @ EXCEPT !.decision = participant[i].forward[i] ] ]
               /\ UNCHANGED <<coordinator>>

\* A timeout may force an abort once the coordinator is dead and no alive
\* participant is still expecting a decision (explicitly accounted for in
\* the last conjunct here).
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants :
                          ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [ participant EXCEPT ![i] = [ @ EXCEPT !.decision = abort ] ]
                     /\ UNCHANGED <<coordinator>>

\* The full participant program now includes forward() and preDecideOnForward().
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
\* (SOME) INVALID PROPERTIES -- unchanged from ACP_SB and still unsatisfied
\* by the timed-out version: they are described in the paper's narrative as
\* intentionally wrong and are not the failures this submission addresses.

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <>(participant[i].decision = abort  \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                         \A j \in participants : participant[j].vote = yes
                     ~>  participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

================================================================================
---- MODULE ACP_NB --------------------------------------------------------------
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB).  It implements a reliable
\* broadcast by forwarding every received decision to all participants before
\* delivering it locally, so a single link failure cannot hide a commitment
\* decision (property AC5).  The change below repairs a TLC bug: an action
\* that delivers a forwarded decision left the entire "participant" variable
\* unspecified instead of updating just the recipient's entry.

EXTENDS ACP_SB

--------------------------------------------------------------------------------

\* Participants now carry a "forward" table; the coordinator is unchanged.
TypeInvParticipantNB  == participant \in [
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
\* Initially nobody has forwarded anything.
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

\* Forward participant i's predecision to participant j (i does not forward to
\* itself).  The decision is stored in i's own forward table first.
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = 
                     [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]
                   ]
                /\ UNCHANGED <<coordinator>>

\* Participant i receives the decision participant j forwarded to it, recording
\* it in its own forward table (its predecision).
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = 
                                [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]
                              ]
                           /\ UNCHANGED <<coordinator>>

\* A participant receives the coordinator's broadcast decision.
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = 
                     [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]
                   ]
                /\ UNCHANGED <<coordinator>>

\* The actual commit/abort decision, once a participant has predecided and
\* confirmed that every other participant already knows it.
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = 
                    [@ EXCEPT !.decision = participant[i].forward[i]]]
               /\ UNCHANGED <<coordinator>>

\* Participant i aborts on timeout: the coordinator is dead, or it never
\* broadcast to someone who is still alive, or a dead participant never
\* forwarded to an alive one.
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED <<coordinator>>

---------------------------------------------------------------------------------

\* N participants: any participant may crash.  Actions are grouped to keep one
\* step per participant.
parProgNB(i,j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) \/ preDecideOnForward(i,j) \/ abortOnTimeout(i)
                  \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)
progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

--------------------------------------------------------------------------------

\* (SOME) INVALID PROPERTIES

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <>(participant[i].decision = abort  \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                         \A j \in participants : participant[j].vote = yes
                     ~>  participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

================================================================================
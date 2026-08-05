---- MODULE ACP_NB ---------------------------------------------------------------
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB).  The non blocking property
\* AC5 is obtained by using a reliable broadcast: upon reception of a broadcast
\* message it is forwarded to all participants before being delivered locally (the
\* local delivery step stores the decision into the sender's own forward slot,
\* since a participant does not forward to itself).  The original module failed in
\* TLC with a partially specified successor: the preDecideOnForward action left
\* the whole participant record untouched (participant' = [participant EXCEPT
\* ! = @]), which assigned no value to a variable that is always in the
\* state-constraint.  The fix is to concretise the update so that participant[i]
\* is fully defined in the successor.

EXTENDS ACP_SB

--------------------------------------------------------------------------------

\* Participants now carry a "forward" variable; coordinator is unchanged.

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

\* forward(i,j): participant i forwards its predecision to participant j.
\* IF i is alive, has a decision (forward[i] # notsent), and has not forwarded to j,
\* THEN participant i stores its decision in participant i's forward slot for j.
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = 
                     [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]
                   ]
                /\ UNCHANGED <<coordinator>>

\* preDecideOnForward(i,j): participant i receives participant j's forwarded decision.
\* IF i is alive, undecided (forward[i] = notsent), and j has forwarded to i,
\* THEN i stores j's decision in its own forward slot.
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = 
                                [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]
                              ]
                           /\ UNCHANGED <<coordinator>>

\* preDecide(i): participant i receives the coordinator's decision.
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = 
                     [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]
                   ]
                /\ UNCHANGED <<coordinator>>

\* decideNB(i): participant i decides once it has predecided and forwarded to all.
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]]
               /\ UNCHANGED <<coordinator>>

\* abortOnTimeout(i): timeout case for an undecided participant.
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive
                                                   => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED <<coordinator>>

--------------------------------------------------------------------------------

parProgNB(i,j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) \/ preDecideOnForward(i,j) \/ abortOnTimeout(i)
                  \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants :
                WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

--------------------------------------------------------------------------------

\* Intended safety properties (still checked against the fixed model).

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                       (\A j \in participants : participant[j].vote = yes)
                         ~> (participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty)

================================================================================
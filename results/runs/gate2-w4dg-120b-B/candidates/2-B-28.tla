---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB).  Messages are
\* reliably broadcast by forwarding: a predecision is first stored in
\* forward[i] and only then delivered to the local site.
\* The change below: the forward action updates the whole participant
\* record, so the next-state relation is complete (not partially
\* specified).

EXTENDS ACP_SB

--------------------------------------------------------------------------------

\* Participants record their (pre)decision in a forward table.
\* Coordinator unchanged.

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

--------------------------------------------------------------------------------

InitParticipantNB == \E f \in [ participants -> {notsent} ] :
                      participant \in [
                        participants -> [
                          vote     : {yes, no},
                          alive    : {TRUE},
                          decision : {undecided},
                          faulty   : {FALSE},
                          voteSent : {FALSE},
                          forward  : f
                        ]
                      ]

InitNB == InitParticipantNB /\ InitCoordinator

--------------------------------------------------------------------------------

\* forward(i,j): participant i forwards its predecision to participant j.
\* The next-state relation writes the whole record (including forward),
\* so no variable is left unassigned.
forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = [
                     vote     |-> @,
                     alive    |-> @,
                     decision |-> @,
                     faulty   |-> @,
                     voteSent |-> @,
                     forward  |-> [@ EXCEPT ![j] = participant[i].forward[i]]
                   ]]
                /\ UNCHANGED coordinator

\* preDecideOnForward(i,j): participant i adopts the decision participant j
\* forwarded to it.
preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = [
                                vote     |-> @,
                                alive    |-> @,
                                decision |-> @,
                                faulty   |-> @,
                                voteSent |-> @,
                                forward  |-> [@ EXCEPT ![i] = participant[j].forward[i]]
                              ]]
                           /\ UNCHANGED coordinator

\* preDecide(i): participant i adopts the coordinator's broadcast.
preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = [
                     vote     |-> @,
                     alive    |-> @,
                     decision |-> @,
                     faulty   |-> @,
                     voteSent |-> @,
                     forward  |-> [@ EXCEPT ![i] = coordinator.broadcast[i]]
                   ]]
                /\ UNCHANGED coordinator

\* decideNB(i): actual decision, after the predecision has been forwarded.
decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = [
                    vote     |-> @,
                    alive    |-> @,
                    decision |-> participant[i].forward[i],
                    faulty   |-> @,
                    voteSent |-> @,
                    forward  |-> @
                  ]]
               /\ UNCHANGED coordinator

\* abortOnTimeout(i): a simulated failure case; see ACP_SB for details.
abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED coordinator

--------------------------------------------------------------------------------

parProgNB(i,j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) \/ preDecideOnForward(i,j)
                  \/ abortOnTimeout(i) \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

--------------------------------------------------------------------------------

\* (SOME) INVALID PROPERTIES (kept as is for the spec's own record)

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <>(participant[i].decision = abort  \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                         \A j \in participants : participant[j].vote = yes
                     ~>  participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
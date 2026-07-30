---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB) using a reliable broadcast.
\* A broadcast message is first delivered to the coordinator and only then
\* forwarded to the participants; this way a participant's decision is not
\* written unless it has already been forwarded onward, which is what guarantees
\* non-blocking progress.

EXTENDS ACP_SB

--------------------------------------------------------------------------------

\* Participants each carry a "forward" map that remembers which decision (if any)
\* was sent to which participant.  These fields were dropped by mistake in the
\* original revision, which is why TLC signals that a next-state action is
\* underspecified, and why all other actions in this file re-write the whole map.

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

TypeInvCoordinator == coordinator \in [
  [ vote      : [ participants -> {waiting, yes, no} ],
    alive     : BOOLEAN,
    decision  : {undecided, commit, abort},
    faulty    : BOOLEAN,
    broadcast : [ participants -> {notsent, commit, abort} ],
    request   : [ participants -> BOOLEAN ]
  ]
]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

--------------------------------------------------------------------------------

\* Initially, participants have not forwarded anything.

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

InitCoordinator == coordinator = [
  vote      |-> [ p \in participants |-> waiting ],
  alive     |-> TRUE,
  decision  |-> undecided,
  faulty    |-> FALSE,
  broadcast |-> [ p \in participants |-> notsent ],
  request   |-> [ p \in participants |-> FALSE ]
]

InitNB == InitParticipantNB /\ InitCoordinator

--------------------------------------------------------------------------------

\* forward(i,j): participant i forwards the predecision it has already received
\* to participant j (i does not forward to itself; j receives it via preDecide).
\* The forward[i] map is re-written entirely, each entry being copied from the
\* old map, so the map is never left with a missing (underspecified) cell.

forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [ participant EXCEPT ![i] = 
                     [ @ EXCEPT !.forward = 
                       [ @ EXCEPT ![j] = participant[i].forward[i] ]
                     ]
                   ]
                /\ UNCHANGED <<coordinator>>

\* preDecideOnForward(i,j): participant i adopts the predecision forwarded to it
\* by participant j.

preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [ participant EXCEPT ![i] = 
                                [ @ EXCEPT !.forward = 
                                  [ @ EXCEPT ![i] = participant[j].forward[i] ]
                                ]
                              ]
                           /\ UNCHANGED <<coordinator>>

\* preDecide(i): participant i adopts the predecision broadcast by the coordinator.

preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [ participant EXCEPT ![i] = 
                     [ @ EXCEPT !.forward = 
                       [ @ EXCEPT ![i] = coordinator.broadcast[i] ]
                     ]
                   ]
                /\ UNCHANGED <<coordinator>>

\* decideNB(i): a (pre)decided participant decides only after it has
\* forwarded that predecision to every other participant.

decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [ participant EXCEPT ![i] = 
                    [ @ EXCEPT !.decision = participant[i].forward[i] ]
                  ]
               /\ UNCHANGED <<coordinator>>

\* abortOnTimeout(i): if the coordinator has gone and no participant has yet
\* predecided, the remaining alive participants abort.

abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [ participant EXCEPT ![i] = [ @ EXCEPT !.decision = abort ] ]
                     /\ UNCHANGED <<coordinator>>

--------------------------------------------------------------------------------

\* Coordinator actions from ACP_SB are unchanged.

coordDie       == /\ coordinator.alive
                  /\ coordinator' = [ coordinator EXCEPT !.alive = FALSE ]
                  /\ UNCHANGED <<participant>>

coordCrash(i)  == coordDie \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)

coordProgN == coordCrash(SuchParticipant) \/ \E i \in participants : coordDecide(i)

\* Participant actions that realize the reliable broadcast.  The forward map
\* must be rewritten each time, or TLC flags the action as underspecified.

parProgNB(i,j) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) \/ preDecideOnForward(i,j) \/ abortOnTimeout(i)
                  \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgN)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

--------------------------------------------------------------------------------

\* (SOME) INVALID PROPERTIES

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <>(participant[i].decision = abort  \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                         \A j \in participants : participant[j].vote = yes
                     ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
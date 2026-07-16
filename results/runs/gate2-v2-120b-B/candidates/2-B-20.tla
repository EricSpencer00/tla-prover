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

VARIABLES participant, coordinator

\* Types
TypeInvParticipantNB == 
  participant \in [
    participants -> [
      vote      : {yes, no}, 
      alive     : BOOLEAN, 
      decision  : {undecided, commit, abort},
      faulty    : BOOLEAN,
      voteSent  : BOOLEAN,
      forward   : [ participants -> {notsent, commit, abort} ]
    ]
  ]

TypeInvCoordinator == 
  coordinator \in [
    vote      : [ participants -> {yes, no, waiting} ],
    alive     : BOOLEAN,
    decision  : {undecided, commit, abort},
    faulty    : BOOLEAN,
    broadcast : [ participants -> {notsent, commit, abort} ],
    request   : [ participants -> BOOLEAN ]
  ]

TypeInv == TypeInvParticipantNB /\ TypeInvCoordinator

\* Initial state
InitParticipantNB == 
  participant \in [
    participants -> [
      vote      : {yes, no},
      alive     : {TRUE},
      decision  : {undecided},
      faulty    : {FALSE},
      voteSent  : {FALSE},
      forward   : [ participants -> {notsent} ]
    ]
  ]

InitCoordinator == 
  coordinator \in [
    vote      : [ participants -> waiting ],
    alive     : TRUE,
    decision  : undecided,
    faulty    : FALSE,
    broadcast : [ participants -> notsent ],
    request   : [ participants -> FALSE ]
  ]

InitNB == InitParticipantNB /\ InitCoordinator

\* Participant actions

forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [ participant EXCEPT ![i] = 
        [ @ EXCEPT !.forward = 
            [ @ EXCEPT ![j] = participant[i].forward[i] ] ] ]
  /\ UNCHANGED coordinator

preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [ participant EXCEPT ![i] = 
        [ @ EXCEPT !.forward = 
            [ @ EXCEPT ![i] = participant[j].forward[i] ] ] ]
  /\ UNCHANGED coordinator

preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [ participant EXCEPT ![i] = 
        [ @ EXCEPT !.forward = 
            [ @ EXCEPT ![i] = coordinator.broadcast[i] ] ] ]
  /\ UNCHANGED coordinator

decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [ participant EXCEPT ![i] = 
        [ @ EXCEPT !.decision = participant[i].forward[i] ] ]
  /\ UNCHANGED coordinator

abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [ participant EXCEPT ![i] = [ @ EXCEPT !.decision = abort ] ]
  /\ UNCHANGED coordinator

\* Placeholder actions imported from ACP_SB (assumed defined there)
sendVote(i) == 
  /\ participant[i].alive
  /\ ~participant[i].voteSent
  /\ participant' = [ participant EXCEPT ![i] = 
        [ @ EXCEPT !.voteSent = TRUE ] ]
  /\ UNCHANGED coordinator

abortOnVote(i) == 
  /\ participant[i].alive
  /\ participant[i].vote = no
  /\ participant' = [ participant EXCEPT ![i] = 
        [ @ EXCEPT !.decision = abort ] ]
  /\ UNCHANGED coordinator

abortOnTimeoutRequest(i) == 
  /\ participant[i].alive
  /\ coordinator.request[i] = FALSE
  /\ participant' = participant
  /\ UNCHANGED coordinator

parProgNB(i, j) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ forward(i, j)
  \/ preDecideOnForward(i, j)
  \/ abortOnTimeout(i)
  \/ preDecide(i)
  \/ decideNB(i)

coordProgN == 
  \E i \in participants :
    /\ coordinator.broadcast[i] # notsent
    /\ coordinator' = [ coordinator EXCEPT !.broadcast[i] = 
          IF coordinator.decision = commit THEN commit ELSE abort ]
    /\ UNCHANGED participant

parProgNNB == 
  \E i, j \in participants : 
    (parDie(i) \/ parProgNB(i, j))

progNNB == parProgNNB \/ coordProgN

fairnessNB ==
  /\ \A i \in participants : WF_<<coordinator, participant>>( \E j \in participants : parProgNB(i, j) )
  /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* Properties (kept unchanged)

AllCommit == \A i \in participants : <> ( participant[i].decision = commit \/ participant[i].faulty )

AllAbort  == \A i \in participants : <> ( participant[i].decision = abort  \/ participant[i].faulty )

AllCommitYesVotes == 
  \A i \in participants :
    \A j \in participants : participant[j].vote = yes
  ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

=============================================================================
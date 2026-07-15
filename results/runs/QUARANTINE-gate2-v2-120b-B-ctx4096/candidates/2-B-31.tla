---- MODULE ACP_NB ----
EXTENDS ACP_SB

\* ----------------------------------------------------------------------
\* Non‑blocking Atomic Commitment Protocol (ACP‑NB)
\* ----------------------------------------------------------------------
\* The non‑blocking property (AC5) is obtained by using a reliable broadcast
\* implemented as follows:
\*   – upon reception of a broadcast message, this message is forwarded to all
\*     participants before it is delivered to the local site;
\*   – since participant *i* does not forward to itself, *forward[i]* is used
\*     to store the decision before it becomes the final *decision*.
\* ----------------------------------------------------------------------

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
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

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
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

InitNB == InitParticipantNB /\ InitCoordinator

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------

\* forward(i,j): participant *i* forwards its pre‑decision to participant *j*
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
  /\ UNCHANGED << coordinator >>

\* preDecideOnForward(i,j): participant *i* receives a forwarded decision from *j*
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
  /\ UNCHANGED << coordinator >>

\* preDecide(i): participant *i* receives the coordinator's broadcast
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
  /\ UNCHANGED << coordinator >>

\* decideNB(i): participant *i* finalises its decision after it has forwarded
\* its (pre)decision to every other participant
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]]
  /\ UNCHANGED << coordinator >>

\* abortOnTimeout(i): simulated timeout leading to abort
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants :
        participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants :
        ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED << coordinator >>

\* ----------------------------------------------------------------------
\* Composite behaviours
\* ----------------------------------------------------------------------
parProgNB(i, j) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ forward(i, j)
  \/ preDecideOnForward(i, j)
  \/ abortOnTimeout(i)
  \/ preDecide(i)
  \/ decideNB(i)

parProgNNB == \E i, j \in participants : parDie(i) \/ parProgNB(i, j)

progNNB == parProgNNB \/ coordProgN

\* Weak fairness for participants and coordinator
fairnessNB ==
  /\ \A i \in participants : WF_<<coordinator, participant>>( \E j \in participants : parProgNB(i, j) )
  /\ WF_<<coordinator, participant>>(coordProgB)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* ----------------------------------------------------------------------
\* (SOME) INVALID PROPERTIES
\* ----------------------------------------------------------------------
AllCommit == \A i \in participants : <> (participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <> (participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes ==
  \A i \in participants :
    ( \A j \in participants : participant[j].vote = yes )
      ~> ( participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty )

==============================================================================
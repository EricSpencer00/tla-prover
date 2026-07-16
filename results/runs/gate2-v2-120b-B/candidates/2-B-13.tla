---- MODULE ACP_NB ------------------------------------------------------------
EXTENDS ACP_SB

\* ---------------------------------------------------------------------------
\* Type invariants
\* ---------------------------------------------------------------------------

ParticipantType == [
  vote      : {yes, no},
  alive     : BOOLEAN,
  decision  : {undecided, commit, abort},
  faulty    : BOOLEAN,
  voteSent  : BOOLEAN,
  forward   : [participants -> {notsent, commit, abort}]
]

CoordinatorType == [
  vote      : [participants -> {waiting, decided}],
  alive     : BOOLEAN,
  decision  : {undecided, commit, abort},
  faulty    : BOOLEAN,
  broadcast : [participants -> {notsent, commit, abort}],
  request   : [participants -> BOOLEAN]
]

TypeInvParticipantNB == participant \in [participants -> ParticipantType]

TypeInvCoordinator == coordinator \in CoordinatorType

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

\* ---------------------------------------------------------------------------
\* Initial state
\* ---------------------------------------------------------------------------

InitParticipantNB == participant = [
  p1 |-> [
    vote      |-> yes,
    alive     |-> TRUE,
    decision  |-> undecided,
    faulty    |-> FALSE,
    voteSent  |-> FALSE,
    forward   |-> [p1 |-> notsent, p2 |-> notsent, p3 |-> notsent]
  ],
  p2 |-> [
    vote      |-> yes,
    alive     |-> TRUE,
    decision  |-> undecided,
    faulty    |-> FALSE,
    voteSent  |-> FALSE,
    forward   |-> [p1 |-> notsent, p2 |-> notsent, p3 |-> notsent]
  ],
  p3 |-> [
    vote      |-> yes,
    alive     |-> TRUE,
    decision  |-> undecided,
    faulty    |-> FALSE,
    voteSent  |-> FALSE,
    forward   |-> [p1 |-> notsent, p2 |-> notsent, p3 |-> notsent]
  ]
]

InitCoordinator == coordinator = [
  vote      |-> [p1 |-> waiting, p2 |-> waiting, p3 |-> waiting],
  alive     |-> TRUE,
  decision  |-> undecided,
  faulty    |-> FALSE,
  broadcast |-> [p1 |-> notsent, p2 |-> notsent, p3 |-> notsent],
  request   |-> [p1 |-> FALSE, p2 |-> FALSE, p3 |-> FALSE]
]

InitNB == InitParticipantNB /\ InitCoordinator

\* ---------------------------------------------------------------------------
\* Actions
\* ---------------------------------------------------------------------------

\* Participant i forwards its predecision to participant j
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i] = 
        [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
  /\ UNCHANGED coordinator

\* Participant i receives a predecision from participant j
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = 
        [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
  /\ UNCHANGED coordinator

\* Participant i receives the decision from the coordinator
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = 
        [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
  /\ UNCHANGED coordinator

\* Participant i decides after having forwarded its predecision to everyone
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT ![i] = 
        [@ EXCEPT !.decision = participant[i].forward[i]]]
  /\ UNCHANGED coordinator

\* Timeout leading to abort for participant i
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants :
        ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

\* Participant i dies (from ACP_SB)
parDie(i) == \E v \in {yes, no} :
                /\ participant[i].alive = TRUE
                /\ participant' = [participant EXCEPT ![i] = 
                      [@ EXCEPT !.alive = FALSE,
                               !.faulty = TRUE,
                               !.decision = abort]]
                /\ UNCHANGED coordinator

\* Coordinator sends a vote request (from ACP_SB)
coordSendRequest(i) ==
  /\ coordinator.alive
  /\ coordinator.request[i] = FALSE
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

\* Coordinator receives a vote from participant i (from ACP_SB)
coordReceiveVote(i) ==
  /\ coordinator.alive
  /\ coordinator.request[i] = TRUE
  /\ participant[i].voteSent = FALSE
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.voteSent = TRUE]]
  /\ UNCHANGED << >>

\* Coordinator decides commit or abort based on collected votes (from ACP_SB)
coordDecide ==
  /\ coordinator.alive
  /\ \A i \in participants : coordinator.request[i] = TRUE
  /\ coordinator' = [coordinator EXCEPT !.decision = 
        IF \A i \in participants : coordinator.vote[i] = yes THEN commit ELSE abort]
  /\ UNCHANGED participant

\* Coordinator broadcasts its decision (from ACP_SB)
coordProgB ==
  \/ coordSendRequest(i)
  \/ coordReceiveVote(i)
  \/ coordDecide
  \/ \E i \in participants :
        /\ coordinator.decision # undecided
        /\ coordinator.broadcast[i] = notsent
        /\ coordinator' = [coordinator EXCEPT
              !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
        /\ UNCHANGED participant

\* Combined participant behavior (non‑blocking version)
parProgNB(i, j) ==
  \/ sendVote(i)                \* from ACP_SB
  \/ abortOnVote(i)             \* from ACP_SB
  \/ abortOnTimeoutRequest(i)   \* from ACP_SB
  \/ forward(i, j)
  \/ preDecideOnForward(i, j)
  \/ abortOnTimeout(i)
  \/ preDecide(i)
  \/ decideNB(i)

\* Non‑deterministic choice of a participant and a partner for the above actions
parProgNNB == \E i, j \in participants : parDie(i) \/ parProgNB(i, j)

\* Overall next‑state relation
progNNB == parProgNNB \/ coordProgB

\* Weak fairness for each participant and for the coordinator
fairnessNB ==
  /\ \A i \in participants :
        WF_<<coordinator, participant>>( \E j \in participants : parProgNB(i, j) )
  /\ WF_<<coordinator, participant>>( coordProgB )

\* Specification
SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* ---------------------------------------------------------------------------
\* (Optional) Invariant statements – unchanged from the original spec
\* ---------------------------------------------------------------------------

AllCommit == \A i \in participants : <> (participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <> (participant[i].decision = abort  \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                         \A j \in participants : participant[j].vote = yes
                     ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

=============================================================================
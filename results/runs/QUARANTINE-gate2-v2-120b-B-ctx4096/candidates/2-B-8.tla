---- MODULE ACP_NB ----
\* Non‑blocking Atomic Commitment Protocol (ACP‑NB) specification.
\* Fixed to ensure every action fully specifies the ``participant`` variable,
\* while preserving the intended behavior of the protocol.

EXTENDS ACP_SB

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLE participant, coordinator

\* ----------------------------------------------------------------------
\* Type invariant (unchanged)
\* ----------------------------------------------------------------------
TypeInvParticipantNB ==
  participant \in [
    participants -> [
      vote      : {yes, no},
      alive     : BOOLEAN,
      decision  : {undecided, commit, abort},
      faulty    : BOOLEAN,
      voteSent  : BOOLEAN,
      forward   : [participants -> {notsent, commit, abort}]
    ]
  ]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

\* ----------------------------------------------------------------------
\* Initial predicate (unchanged)
\* ----------------------------------------------------------------------
InitParticipantNB ==
  participant \in [
    participants -> [
      vote     : {yes, no},
      alive    : {TRUE},
      decision : {undecided},
      faulty   : {FALSE},
      voteSent : {FALSE},
      forward  : [participants -> {notsent}]
    ]
  ]

InitNB == InitParticipantNB /\ InitCoordinator

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Forward a decision from i to j
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' =
        [participant EXCEPT ![i] =
           [@ EXCEPT !.forward =
                [@ EXCEPT ![j] = participant[i].forward[i]]
           ]
        ]
  /\ UNCHANGED coordinator

\* Receive a forwarded decision from j
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' =
        [participant EXCEPT ![i] =
           [@ EXCEPT !.forward =
                [@ EXCEPT ![i] = participant[j].forward[i]]
           ]
        ]
  /\ UNCHANGED coordinator

\* Receive the coordinator's broadcast
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' =
        [participant EXCEPT ![i] =
           [@ EXCEPT !.forward =
                [@ EXCEPT ![i] = coordinator.broadcast[i]]
           ]
        ]
  /\ UNCHANGED coordinator

\* Commit the (pre)decision after it has been forwarded to everyone
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' =
        [participant EXCEPT ![i] =
           [@ EXCEPT !.decision = participant[i].forward[i]]
        ]
  /\ UNCHANGED coordinator

\* Abort on timeout (unchanged)
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants :
        ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' =
        [participant EXCEPT ![i] =
           [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

\* ----------------------------------------------------------------------
\* Composite participant program (unchanged except for the fixed actions)
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

parProgNNB ==
  \E i, j \in participants : parDie(i) \/ parProgNB(i, j)

progNNB ==
  parProgNNB \/ coordProgN

\* ----------------------------------------------------------------------
\* Fairness (unchanged)
\* ----------------------------------------------------------------------
fairnessNB ==
  /\ \A i \in participants :
        WF_<<coordinator, participant>>( \E j \in participants : parProgNB(i, j) )
  /\ WF_<<coordinator, participant>>(coordProgB)

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
SpecNB ==
  InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* ----------------------------------------------------------------------
\* Invariants (unchanged)
\* ----------------------------------------------------------------------
AllCommit ==
  \A i \in participants :
      <> (participant[i].decision = commit \/ participant[i].faulty)

AllAbort ==
  \A i \in participants :
      <> (participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes ==
  \A i \in participants :
    (\A j \in participants : participant[j].vote = yes)
    ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
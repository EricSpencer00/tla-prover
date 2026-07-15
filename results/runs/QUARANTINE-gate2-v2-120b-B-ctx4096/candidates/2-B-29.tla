---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Commit Protocol (ACP-NB) with reliable broadcast.
\* The implementation forwards a received decision to all other participants
\* before delivering it locally.  The variable \`forward[i]\` stores the decision
\* that participant *i* has learned (either from the coordinator or from another
\* participant) but has not yet delivered as its final decision.

EXTENDS ACP_SB

\***************************************************************************
\* Type invariants
\***************************************************************************
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

TypeInvCoordinator ==
  coordinator \in [
    vote       : [participants -> {yes, no, waiting}],
    alive      : BOOLEAN,
    decision   : {undecided, commit, abort},
    faulty     : BOOLEAN,
    broadcast  : [participants -> {notsent, commit, abort}],
    request    : [participants -> BOOLEAN]
  ]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

\***************************************************************************
\* Initial state
\***************************************************************************
InitParticipantNB ==
  participant \in [
    participants -> [
      vote      : {yes, no},
      alive     : TRUE,
      decision  : undecided,
      faulty    : FALSE,
      voteSent  : FALSE,
      forward   : [participants -> notsent]
    ]
  ]

InitCoordinator ==
  coordinator = [
    vote       |-> [p \in participants |-> waiting],
    alive      |-> TRUE,
    decision   |-> undecided,
    faulty     |-> FALSE,
    broadcast  |-> [p \in participants |-> notsent],
    request    |-> [p \in participants |-> FALSE]
  ]

InitNB == InitParticipantNB /\ InitCoordinator

\***************************************************************************
\* Actions
\***************************************************************************
\* Forward the pre‑decision from i to j (i ≠ j)
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent          \* i has a pre‑decision
  /\ participant[i].forward[j] = notsent          \* not yet forwarded to j
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT
                !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]
               ]
      ]
  /\ UNCHANGED coordinator

\* Participant i adopts the decision that j has already forwarded to i
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent          \* i has not yet pre‑decided
  /\ participant[j].forward[i] # notsent          \* j has forwarded to i
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT
                !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]
               ]
      ]
  /\ UNCHANGED coordinator

\* Participant i adopts the decision broadcast by the coordinator
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT
                !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]
               ]
      ]
  /\ UNCHANGED coordinator

\* After having forwarded its pre‑decision to all others, i makes the final decision
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT
                !.decision = participant[i].forward[i]
               ]
      ]
  /\ UNCHANGED coordinator

\* Timeout abort: if the coordinator is dead and no alive participant can still
\* receive a decision, then every alive undecided participant aborts.
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants :
        participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants :
        ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT
        ![i] = [@ EXCEPT !.decision = abort]
      ]
  /\ UNCHANGED coordinator

\* Placeholder for actions defined in the underlying ACP_SB specification
sendVote(i)               == SendVote(i)               \* from ACP_SB
abortOnVote(i)            == AbortOnVote(i)            \* from ACP_SB
abortOnTimeoutRequest(i) == AbortOnTimeoutRequest(i) \* from ACP_SB
coordProgB                == CoordProgB                \* from ACP_SB

\* Participant's nondeterministic program
parProgNB(i, j) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ forward(i, j)
  \/ preDecideOnForward(i, j)
  \/ abortOnTimeout(i)
  \/ preDecide(i)
  \/ decideNB(i)

\* Overall system program
parProgNNB == \E i, j \in participants : parProgNB(i, j)

progNNB == parProgNNB \/ coordProgB

\***************************************************************************
\* Fairness
\***************************************************************************
fairnessNB ==
  /\ \A i \in participants :
        WF_<<coordinator, participant>>( \E j \in participants : parProgNB(i, j) )
  /\ WF_<<coordinator, participant>>(coordProgB)

\***************************************************************************
\* Specification
\***************************************************************************
SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\***************************************************************************
\* Invariant (kept unchanged from the original file)
\***************************************************************************
AllCommit == \A i \in participants : <> (participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <> (participant[i].decision = abort  \/ participant[i].faulty)

AllCommitYesVotes ==
  \A i \in participants :
    \A j \in participants : participant[j].vote = yes
      ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
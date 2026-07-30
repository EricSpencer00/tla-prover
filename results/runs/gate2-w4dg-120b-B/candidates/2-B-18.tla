---- MODULE ACP_NB ----
\* Non blocking Atomic Commit Protocol over a reliable broadcast.
\* A participant forwards a received decision to every other participant
\* before delivering it locally (forward, preDecideOnForward, decideNB).
\* The invariant AllCommitYesVotes is kept: a committed decision is only
\* reachable if every participant voted yes (a correct protocol outcome).
EXTENDS ACP_SB

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
    vote       : [participants -> {waiting, yes, no}],
    alive      : BOOLEAN,
    decision   : {undecided, commit, abort},
    faulty     : BOOLEAN,
    broadcast  : [participants -> {notsent, commit, abort}],
    request    : [participants -> BOOLEAN]
  ]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

InitParticipantNB ==
  participant \in [
    participants -> [
      vote      |-> {yes, no},
      alive     |-> {TRUE},
      decision  |-> {undecided},
      faulty    |-> {FALSE},
      voteSent  |-> {FALSE},
      forward   |-> [participants -> {notsent}]
    ]
  ]

InitCoordinator ==
  coordinator = [
    vote       |-> [participants -> waiting],
    alive      |-> TRUE,
    decision   |-> undecided,
    faulty     |-> FALSE,
    broadcast  |-> [participants -> notsent],
    request    |-> [participants -> FALSE]
  ]

InitNB == InitParticipantNB /\ InitCoordinator

\* forwarding of a predecision from participant i to participant j
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
  /\ UNCHANGED coordinator

\* participant i receives decision from participant j and adopts it pre-locally
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
  /\ UNCHANGED coordinator

\* participant i receives decision from coordinator (pre-locally)
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
  /\ UNCHANGED coordinator

\* actual decision: i decides once its predecision has been forwarded to everyone
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]]
  /\ UNCHANGED coordinator

\* participant i times out (coordinator died without deciding) and aborts
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

\* vote, abort on vote, and timeout-vote controls from ACP_SB are unchanged
parProg(i, j) ==
  \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
  \/ forward(i, j) \/ preDecideOnForward(i, j) \/ abortOnTimeout(i) \/ preDecide(i) \/ decideNB(i)

parProgN == \E i, j \in participants : parDie(i) \/ parProg(i, j)

progN == parProgN \/ coordProgN

fairnessN ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProg(i, j))
  /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progN]_<<coordinator, participant>> /\ fairnessN

\* A committed decision requires unanimity: every participant voted yes.
AllCommitYesVotes ==
  \A i \in participants :
    (\A j \in participants : participant[j].vote = yes)
      ~> (participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty)

====
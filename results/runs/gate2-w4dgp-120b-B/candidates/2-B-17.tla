---- MODULE ACP_NB -------------------------------------------------------------
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB)
\* The non blocking property AC5 is obtained by using a reliable broadcast
\* implemented as follows:
\*   - upon reception of a broadcast message, this message is forwarded to all
\*     participants before it is delivered to the local site;
\*   - since a participant does not forward to itself, the forwarded decision is
\*     stored in a separate "forward" component before it is delivered locally.
\* Compared to the safe-commit baseline ACP_SB, ACP-NB adds the "forward"
\* component to the participant record and replaces the single decision step
\* by a predecision (forwarding + delivery) followed by a decision step.

EXTENDS ACP_SB

\* Participants now carry a "forward" component: the decisions they have
\* forwarded to each other participant (indexed by recipient).  Coordinator
\* type is unchanged.

TypeInvParticipantNB ==
  participant \in [
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

\* Initially no participant has forwarded anything.

InitParticipantNB ==
  participant \in [
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

\* Forward a forwarded decision (i -> j): participant i is alive, i has a
\* predecision stored in forward[i], and i has not yet forwarded it to j.
\* The forwarded value is copied into forward[j] (j's predecision buffer).
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i] =
        [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
  /\ UNCHANGED <<coordinator>>

\* Deliver a predecision received from another participant (i <- j):
\* participant i is alive, i has no predecision yet, and j has already
\* forwarded one to i.
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT ![i] =
        [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
  /\ UNCHANGED <<coordinator>>

\* Deliver the coordinator's broadcasted decision to participant i.
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] =
        [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
  /\ UNCHANGED <<coordinator>>

\* A participant decides once it has forwarded (or received) its
\* predecision to all participants, including itself.
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT ![i] =
        [@ EXCEPT !.decision = participant[i].forward[i]]]
  /\ UNCHANGED <<coordinator>>

\* Abandon the transaction on timeout: coordinator dead before sending, or
\* a participant still undecided with no live sender of a decision.
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants :
       (~participant[j].alive /\ participant[k].alive) => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED <<coordinator>>

\* For N participants, the protocol is a disjunction over participant pairs
\* for the forwarding/delivery actions, plus the baseline actions.

parProgNB(i, j) ==
  \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
  \/ forward(i, j) \/ preDecideOnForward(i, j)
  \/ abortOnTimeout(i) \/ preDecide(i) \/ decideNB(i)

parProgNNB == \E i, j \in participants : parDie(i) \/ parProgNB(i, j)

progNNB == parProgNNB \/ coordProgN

fairnessNB ==
  /\ \A i \in participants :
        WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i, j))
  /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* (SOME) INVALID PROPERTIES: these must stay untouched by the fix; they
\* are not part of the linting requirement, but are reproduced here for
\* completeness.

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <>(participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes ==
  \A i \in participants :
    \A j \in participants : participant[j].vote = yes
      ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

====
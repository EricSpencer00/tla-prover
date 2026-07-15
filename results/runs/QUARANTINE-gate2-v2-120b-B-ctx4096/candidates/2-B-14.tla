---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Commitment Protocol (ACP-NB)
\* The non blocking property AC5 is obtained by using a reliable broadcast 
\* implemented as follows:
\*   - upon reception of a broadcast message, this message is forwarded to all
\*     participants before it's delivered to the local site;
\*   - since participant i does not forward to itself, forward[i] is used to 
\*     store the decision before it's delivered (and becomes "decision")

EXTENDS ACP_SB

\*----------------------------------------------------------------------
\* Types
\*----------------------------------------------------------------------
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

TypeInvCoordinator ==  coordinator \in [
    participants -> [
      vote      : {yes, no, waiting},
      broadcast : [participants -> {notsent, commit, abort}]
    ],
    alive     : BOOLEAN,
    decision  : {undecided, commit, abort},
    faulty    : BOOLEAN,
    request   : [participants -> BOOLEAN]
  ]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

\*----------------------------------------------------------------------
\* Initialization
\*----------------------------------------------------------------------
InitParticipantNB ==
  participant \in [
    participants -> [
      vote     : {yes, no},
      alive    : TRUE,
      decision : undecided,
      faulty   : FALSE,
      voteSent : FALSE,
      forward  : [participants -> notsent]
    ]
  ]

InitCoordinator ==
  coordinator \in [
    vote      : [participants -> waiting],
    broadcast : [participants -> notsent],
    alive     : TRUE,
    decision  : undecided,
    faulty    : FALSE,
    request   : [participants -> FALSE]
  ]

InitNB == InitParticipantNB /\ InitCoordinator

\*----------------------------------------------------------------------
\* Actions
\*----------------------------------------------------------------------
\* forward(i,j): participant i forwards its predecision to participant j
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i] =
        [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
  /\ UNCHANGED coordinator

\* preDecideOnForward(i,j): participant i receives decision from participant j
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT ![i] =
        [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
  /\ UNCHANGED coordinator

\* preDecide(i): participant i receives decision from coordinator
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] =
        [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
  /\ UNCHANGED coordinator

\* decideNB(i): participant i makes its final decision
decideNB(i) ==
  /\ participant[i].alive
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]]
  /\ UNCHANGED coordinator

\* abortOnTimeout(i): simulated timeout leading to abort
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants :
        ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

\* parProgNB(i,j): combined participant behavior for a pair (i,j)
parProgNB(i, j) ==
  \/ forward(i, j)
  \/ preDecideOnForward(i, j)
  \/ preDecide(i)
  \/ decideNB(i)
  \/ abortOnTimeout(i)

\* parProgNNB: existentially quantified participant actions
parProgNNB ==
  \E i, j \in participants : parProgNB(i, j)

\* coordProgN: coordinator actions are taken from ACP_SB (imported)
coordProgN == coordProgB

\*----------------------------------------------------------------------
\* Fairness
\*----------------------------------------------------------------------
fairnessNB ==
  /\ \A i \in participants :
        WF_<<coordinator, participant>>( \E j \in participants : parProgNB(i, j) )
  /\ WF_<<coordinator, participant>>(coordProgB)

\*----------------------------------------------------------------------
\* Specification
\*----------------------------------------------------------------------
SpecNB == InitNB /\ [][parProgNNB \/ coordProgN]_<<coordinator, participant>> /\ fairnessNB

\*----------------------------------------------------------------------
\* (SOME) INVALID PROPERTIES 
\*----------------------------------------------------------------------
AllCommit ==
  \A i \in participants :
    <> ( participant[i].decision = commit \/ participant[i].faulty )

AllAbort ==
  \A i \in participants :
    <> ( participant[i].decision = abort \/ participant[i].faulty )

AllCommitYesVotes ==
  \A i \in participants :
    \A j \in participants : participant[j].vote = yes
    ~> participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

=============================================================================
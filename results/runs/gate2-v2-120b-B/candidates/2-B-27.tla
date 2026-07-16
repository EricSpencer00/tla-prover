---- MODULE ACP_NB ----
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non‑blocking Atomic Commitment Protocol (ACP‑NB)

EXTENDS ACP_SB

\* ----------------------------------------------------------------------
\*  Type invariants
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
\*  Initialization
\* ----------------------------------------------------------------------
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

\* ----------------------------------------------------------------------
\*  Actions
\* ----------------------------------------------------------------------
\* Forward a pre‑decision from i to j
forward(i, j) ==
    /\ i # j
    /\ participant[i].alive
    /\ participant[i].forward[i] # notsent
    /\ participant[i].forward[j] = notsent
    /\ participant' =
        [participant EXCEPT ![i] =
            [@ EXCEPT !.forward = [@ EXCEPT ![j] = participant[i].forward[i]]]]
    /\ UNCHANGED <<coordinator>>

\* Participant i adopts the decision forwarded by participant j
preDecideOnForward(i, j) ==
    /\ i # j
    /\ participant[i].alive
    /\ participant[i].forward[i] = notsent
    /\ participant[j].forward[i] # notsent
    /\ participant' =
        [participant EXCEPT ![i] =
            [@ EXCEPT !.forward = [@ EXCEPT ![i] = participant[j].forward[i]]]]
    /\ UNCHANGED <<coordinator>>

\* Participant i adopts the decision broadcast by the coordinator
preDecide(i) ==
    /\ participant[i].alive
    /\ participant[i].forward[i] = notsent
    /\ coordinator.broadcast[i] # notsent
    /\ participant' =
        [participant EXCEPT ![i] =
            [@ EXCEPT !.forward = [@ EXCEPT ![i] = coordinator.broadcast[i]]]]
    /\ UNCHANGED <<coordinator>>

\* After having forwarded its (pre)decision to everyone, i records the final decision
decideNB(i) ==
    /\ participant[i].alive
    /\ \A j \in participants : participant[i].forward[j] # notsent
    /\ participant' =
        [participant EXCEPT ![i] = [@ EXCEPT !.decision = participant[i].forward[i]]]
    /\ UNCHANGED <<coordinator>>

\* Abort when a timeout is detected (simulated condition)
abortOnTimeout(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ ~coordinator.alive
    /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
    /\ \A j, k \in participants :
          ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
    /\ participant' =
        [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
    /\ UNCHANGED <<coordinator>>

\* ----------------------------------------------------------------------
\*  Combined participant program (parameterised by two participants)
\* ----------------------------------------------------------------------
parProgNB(i, j) ==
    \/ forward(i, j)
    \/ preDecideOnForward(i, j)
    \/ preDecide(i)
    \/ decideNB(i)
    \/ abortOnTimeout(i)

\* ----------------------------------------------------------------------
\*  Global program
\* ----------------------------------------------------------------------
parProgNNB ==
    \E i, j \in participants :
        parProgNB(i, j) \/ parDie(i)

progNNB ==
    parProgNNB \/ coordProgN

fairnessNB ==
    /\ \A i \in participants :
          WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i, j))
    /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB ==
    InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

\* ----------------------------------------------------------------------
\*  (Some) invalid properties – retained unchanged
\* ----------------------------------------------------------------------
AllCommit ==
    \A i \in participants : <> (participant[i].decision = commit \/ participant[i].faulty)

AllAbort ==
    \A i \in participants : <> (participant[i].decision = abort \/ participant[i].faulty)

AllCommitYesVotes ==
    \A i \in participants :
        (\A j \in participants : participant[j].vote = yes)
        ~> (participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty)

====
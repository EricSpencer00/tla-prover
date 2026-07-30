---- MODULE ACP_SB ----
EXTENDS Naturals

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB).  A single
\* coordinator collects votes from a set of participants and then
\* broadcasts a commit or abort decision.  The broadcast is simple
\* (sequential), so a coordinator crash during broadcast can strand
\* participants without a decision, which is why this variant is
\* blocking and does not guarantee termination for every non-faulty
\* participant.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordinator, participant

vars == << coordinator, participant >>

CoordType == [sentVoteReq: [participants -> BOOLEAN],
              voteRcvd: [participants -> {yes, no, waiting}],
              decision: {commit, abort, undecided},
              broadcast: [participants -> {notsent, commit, abort}],
              alive: BOOLEAN, faulty: BOOLEAN]

ParticipantRec == [vote: {yes, no},
                   alive: BOOLEAN, decision: {commit, abort, undecided},
                   faulty: BOOLEAN, sentVote: BOOLEAN]

TypeInv ==
    /\ coordinator \in CoordType
    /\ participant \in [participants -> ParticipantRec]

InitCoordinator ==
    [sentVoteReq |-> [p \in participants |-> FALSE],
     voteRcvd |-> [p \in participants |-> waiting],
     decision |-> undecided,
     broadcast |-> [p \in participants |-> notsent],
     alive |-> TRUE, faulty |-> FALSE]

InitParticipant ==
    [p \in participants |->
        [vote |-> IF TRUE THEN yes ELSE no,
         alive |-> TRUE, decision |-> undecided,
         faulty |-> FALSE, sentVote |-> FALSE]]

Init == /\ coordinator = InitCoordinator
        /\ participant = InitParticipant

\* Coordinator actions
SendVoteReq(p) ==
    /\ coordinator.alive
    /\ ~ coordinator.sentVoteReq[p]
    /\ coordinator' = [coordinator EXCEPT !.sentVoteReq[p] = TRUE]
    /\ UNCHANGED participant

ReceiveVote(p) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ coordinator.sentVoteReq[p]
    /\ coordinator.voteRcvd[p] = waiting
    /\ participant[p].sentVote
    /\ coordinator' = [coordinator EXCEPT !.voteRcvd[p] = participant[p].vote]
    /\ UNCHANGED participant

DetectFault(p) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ coordinator.sentVoteReq[p]
    /\ coordinator.voteRcvd[p] = waiting
    /\ ~ participant[p].alive
    /\ coordinator' = [coordinator EXCEPT !.decision = abort]
    /\ UNCHANGED participant

MakeDecision ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \A p \in participants: coordinator.voteRcvd[p] # waiting
    /\ coordinator' = [coordinator EXCEPT !.decision =
                          IF \A p \in participants: coordinator.voteRcvd[p] = yes
                          THEN commit ELSE abort]
    /\ UNCHANGED participant

BroadcastDecision(p) ==
    /\ coordinator.alive
    /\ coordinator.decision # undecided
    /\ coordinator.broadcast[p] = notsent
    /\ coordinator' = [coordinator EXCEPT !.broadcast[p] = coordinator.decision]
    /\ UNCHANGED participant

CoordDie ==
    /\ coordinator.alive
    /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
    /\ UNCHANGED participant

\* Participant actions
SendVote(p) ==
    /\ participant[p].alive
    /\ coordinator.sentVoteReq[p]
    /\ ~ participant[p].sentVote
    /\ participant' = [participant EXCEPT ![p].sentVote = TRUE]
    /\ UNCHANGED coordinator

AbortOnVote(p) ==
    /\ participant[p].alive
    /\ participant[p].decision = undecided
    /\ participant[p].sentVote
    /\ participant[p].vote = no
    /\ participant' = [participant EXCEPT ![p].decision = abort]
    /\ UNCHANGED coordinator

AbortNoReq(p) ==
    /\ participant[p].alive
    /\ participant[p].decision = undecided
    /\ ~ coordinator.sentVoteReq[p]
    /\ ~ coordinator.alive
    /\ participant' = [participant EXCEPT ![p].decision = abort]
    /\ UNCHANGED coordinator

DecideFromCoordinator(p) ==
    /\ participant[p].alive
    /\ participant[p].decision = undecided
    /\ coordinator.broadcast[p] # notsent
    /\ participant' = [participant EXCEPT ![p].decision = coordinator.broadcast[p]]
    /\ UNCHANGED coordinator

ParticipantDie(p) ==
    /\ participant[p].alive
    /\ participant' = [participant EXCEPT ![p].alive = FALSE, ![p].faulty = TRUE]
    /\ UNCHANGED coordinator

Next ==
    \/ \E p \in participants: SendVoteReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ \E p \in participants: BroadcastDecision(p)
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortNoReq(p)
    \/ \E p \in participants: DecideFromCoordinator(p)
    \/ \E p \in participants: ParticipantDie(p)
    \/ MakeDecision
    \/ CoordDie

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in participants: SendVote(p))
        /\ WF_vars(\E p \in participants: AbortOnVote(p))
        /\ WF_vars(\E p \in participants: DecideFromCoordinator(p))
        /\ WF_vars(MakeDecision)
        /\ WF_vars(\E p \in participants: BroadcastDecision(p))

\* Safety: no two participants decide differently, and commit/abort are
\* backed by unanimous yes or a detected fault, respectively.
Agreement ==
    \A a, b \in participants:
        (participant[a].decision = commit /\ participant[b].decision = abort)
            \/ (participant[a].decision = abort /\ participant[b].decision = commit)

CommitValidity ==
    \A p \in participants: participant[p].decision = commit =>
        (\A q \in participants: participant[q].vote = yes)

AbortValidity ==
    \A p \in participants: participant[p].decision = abort =>
        \/ \E q \in participants: participant[q].vote = no
        \/ \E q \in participants: participant[q].faulty
        \/ coordinator.faulty

Irreversible ==
    \A a, b \in participants:
        (a # b /\ participant[a].decision = commit /\ participant[b].decision = undecided)
            \/ (a # b /\ participant[a].decision = abort /\ participant[b].decision = undecided)

EventualDecision ==
    <>(\A p \in participants: participant[p].decision # undecided
        \/ \E q \in participants: participant[q].faulty \/ coordinator.faulty)

====
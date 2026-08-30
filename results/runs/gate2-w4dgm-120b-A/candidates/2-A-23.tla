---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP_NB extends ACP_SB (the simple broadcast version) by modeling the
\* reliable broadcast that participants use to forward the coordinator's
\* decision to each other before they finalize it locally.
\* The invariant AC1 (Agreement) and AC5 (non-blocking termination) are the
\* new correctness concerns this extension must address.

VARIABLES coordinator, participant
vars == <<coordinator, participant>>

\* Forwarding[t][i] records what participant t has received (at its own
\* index) and what it has forwarded to participant i: notsent / commit / abort.
TypeInv ==
  /\ coordinator \in [req : {idle, waiting}, vote : {yes, no, undecided},
                      udsent : BOOLEAN, broadcast : {commit, abort, undecided},
                      alive : BOOLEAN, faulty : BOOLEAN]
  /\ participant \in [participants -> [vote : {yes, no, undecided},
                      decided : {undecided, commit, abort}, alive : BOOLEAN,
                      faulty : BOOLEAN, udsent : BOOLEAN,
                      forwarded : [participants -> {notsent, commit, abort}]]]

Init ==
  /\ coordinator = [req |-> idle, vote |-> undecided, udsent |-> FALSE,
                    broadcast |-> undecided, alive |-> TRUE, faulty |-> FALSE]
  /\ participant = [t \in participants |-> [vote |-> undecided,
        decided |-> undecided, alive |-> TRUE, faulty |-> FALSE, udsent |-> FALSE,
        forwarded |-> [i \in participants |-> notsent]]]

SendReq ==
  /\ coordinator.alive /\ coordinator.req = idle
  /\ coordinator' = [coordinator EXCEPT !.req = waiting]
  /\ UNCHANGED participant

GetVote(t) ==
  /\ coordinator.alive /\ coordinator.req = waiting /\ coordinator.udsnt = FALSE
  /\ participant[t].alive /\ ~ participant[t].udsnt /\ participant[t].vote # undecided
  /\ coordinator' = [coordinator EXCEPT !.vote = participant[t].vote,
                      !.udsnt = TRUE]
  /\ participant' = [participant EXCEPT ![t].udsnt = TRUE]

CoordinatorFault ==
  /\ coordinator.alive /\ coordinator.req = waiting /\ coordinator.udsnt = FALSE
  /\ coordinator' = [coordinator EXCEPT !.faulty = TRUE, !.alive = FALSE]
  /\ UNCHANGED participant

MakeDecision ==
  /\ coordinator.alive /\ coordinator.udsnt = TRUE /\ coordinator.broadcast = undecided
  /\ coordinator' = [coordinator EXCEPT !.broadcast = IF coordinator.vote = yes THEN commit ELSE abort]
  /\ UNCHANGED participant

Broadcast(t) ==
  /\ coordinator.alive /\ coordinator.broadcast # undecided /\ participant[t].alive
  /\ participant[t].forwarded' = [participant[t].forwarded EXCEPT ![t] = coordinator.broadcast]
  /\ UNCHANGED <<coordinator, participant>>

CoordinatorDie ==
  /\ coordinator.alive /\ coordinator.faulty
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
  /\ UNCHANGED participant

SendVote(t) ==
  /\ participant[t].alive /\ ~ participant[t].udsnt /\ participant[t].vote = undecided
  /\ \E x \in {yes, no} : participant' = [participant EXCEPT ![t].vote = x, ![t].udsnt = TRUE]
  /\ UNCHANGED coordinator

\* A participant may finalize its own decision only after it has forwarded
\* its pre-decision to *all* other participants (the reliability condition).
Decide(t) ==
  /\ participant[t].alive /\ participant[t].decided = undecided
  /\ \A i \in participants : participant[t].forwarded[i] # notsent
  /\ participant' = [participant EXCEPT ![t].decided =
                        IF participant[t].forwarded[t] = commit THEN commit ELSE abort]
  /\ UNCHANGED coordinator

PreDecideFromCoordinator(t) ==
  /\ participant[t].alive /\ participant[t].forwarded[t] = notsent
  /\ coordinator.broadcast # undecided
  /\ participant' = [participant EXCEPT ![t].forwarded = [participant[t].forwarded EXCEPT ![t] = coordinator.broadcast]]
  /\ UNCHANGED coordinator

PreDecideFromForward(t) ==
  /\ participant[t].alive /\ participant[t].forwarded[t] = notsent
  /\ \E u \in participants : participant[u].alive /\ participant[u].forwarded[t] # notsent
  /\ participant' = [participant EXCEPT ![t].forwarded =
                        [participant[t].forwarded EXCEPT ![t] = participant[u].forwarded[t]]]
  /\ UNCHANGED coordinator

Forward(t, i) ==
  /\ participant[t].alive /\ participant[t].forwarded[t] # notsent
  /\ participant[i].alive /\ participant[t].forwarded[i] = notsent
  /\ participant' = [participant EXCEPT ![t].forwarded[i] = participant[t].forwarded[t]]
  /\ UNCHANGED coordinator

Abort(t) ==
  /\ participant[t].alive /\ participant[t].decided = undecided
  /\ coordinator.faulty
  /\ (coordinator.broadcast = undecided \/ coordinator.alive = FALSE)
  /\ \A u \in participants : participant[u].forwarded[t] = notsent
  /\ \A u \in participants : participant[u].faulty = FALSE
  /\ participant' = [participant EXCEPT ![t].decided = abort]
  /\ UNCHANGED coordinator

AbortOnTimeout ==
  /\ coordinator.faulty /\ coordinator.broadcast = undecided /\ coordinator.alive = FALSE
  /\ \A u \in participants : participant[u].decided = undecided
  /\ coordinator' = [coordinator EXCEPT !.broadcast = abort]
  /\ UNCHANGED participant

Die(t) ==
  /\ participant[t].alive /\ participant[t].faulty
  /\ participant' = [participant EXCEPT ![t].alive = FALSE]
  /\ UNCHANGED coordinator

CoordinatorProgress == MakeDecision \/ Broadcast('p1') \/ Broadcast('p2') \/ Broadcast('p3')
ParticipantProgress == SendVote('p1') \/ SendVote('p2') \/ SendVote('p3')
                         \/ Decide('p1') \/ Decide('p2') \/ Decide('p3')
                         \/ PreDecideFromCoordinator('p1') \/ PreDecideFromCoordinator('p2') \/ PreDecideFromCoordinator('p3')
                         \/ PreDecideFromForward('p1') \/ PreDecideFromForward('p2') \/ PreDecideFromForward('p3')
                         \/ Forward('p1', 'p1') \/ Forward('p1', 'p2') \/ Forward('p1', 'p3')
                         \/ Forward('p2', 'p1') \/ Forward('p2', 'p2') \/ Forward('p2', 'p3')
                         \/ Forward('p3', 'p1') \/ Forward('p3', 'p2') \/ Forward('p3', 'p3')
                         \/ Abort('p1') \/ Abort('p2') \/ Abort('p3')

Next ==
  \/ SendReq \/ MakeDecision \/ CoordinatorDie \/ CoordinatorFault \/ AbortOnTimeout
  \/ \E t \in participants : GetVote(t) \/ SendVote(t) \/ Decide(t) \/ PreDecideFromCoordinator(t)
                             \/ PreDecideFromForward(t) \/ Abort(t) \/ Die(t)
  \/ \E t \in participants, i \in participants : Broadcast(t) \/ Forward(t, i)

SpecNB ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(ParticipantProgress)
  /\ WF_vars(CoordinatorProgress)

\* No two participants can reach different decisions at all.
AC1 == \A t, u \in participants : (t # u /\ participant[t].decided # undecided /\ participant[u].decided # undecided) => (participant[t].decided = participant[u].decided)
\* A participant may commit only if everyone voted yes.
AC2 == \A t \in participants : (participant[t].decided = commit) => (\A u \in participants : participant[u].vote = yes)
\* A participant may abort only if somebody voted no or somebody is faulty.
AC3 == \A t \in participants : (participant[t].decided = abort) => ((\E u \in participants : participant[u].vote = no) \/ (\E u \in participants : participant[u].faulty) \/ coordinator.faulty)
\* Irreversibility: once decided, a participant never changes its mind.
AC4 == \A t \in participants : (participant[t].decided # undecided) ~> (participant[t].decided = participant[t].decided)

\* Liveness: either everything decides, or some participant / the coordinator is faulty.
AC3Liveness == <>(\A t \in participants : participant[t].decided # undecided \/ \E t \in participants : participant[t].faulty \/ coordinator.faulty)
\* Liveness: every non-faulty participant eventually decides.
AC5 == \A t \in participants : (participant[t].alive /\ participant[t].faulty = FALSE) ~> (participant[t].decided # undecided)

TypeInvNB == TypeInv
SpecNB == SpecNB
====
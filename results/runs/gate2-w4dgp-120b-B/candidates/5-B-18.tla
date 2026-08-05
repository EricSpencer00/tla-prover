---- MODULE ACP_SB ----
EXTENDS Naturals

\* Time-stamp: <28 Jun 2002 at 18:24:38 by charpov on berlioz.cs.unh.edu>

\* Atomic Commitment with a Simple Broadcast primitive (ACP-SB).  This is a version
\* of the protocol from Sape Mullender's Distributed Systems book (1993) with
\* synchronous communication replaced by asynchronous messages and failures
\* detected "magically".  The broadcast primitive is simple, so the protocol
\* can be stuck waiting for one participant's message while the others have
\* already decided (property AC5 does not hold, which is intentional).

CONSTANTS
  participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
  participant, coordinator

\* participant: each participant's vote, liveness, decision, faulty flag, and
\* whether it has sent its vote.  coordinator: broadcast requests sent, votes
\* received, which participants have been broadcast the decision, the decision
\* itself, liveness, and a faulty flag.
TypeInvParticipant == participant \in [
  participants ->
    [ vote     : {yes, no}, alive    : BOOLEAN,
      decision : {undecided, commit, abort},
      faulty   : BOOLEAN, voteSent : BOOLEAN ]
]

TypeInvCoordinator == coordinator \in [
  [participants -> BOOLEAN], [participants -> {waiting, yes, no}],
  [participants -> {commit, abort, notsent}], {commit, abort, undecided},
  BOOLEAN, BOOLEAN
]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

Init == /\ \A i \in participants :
           participant[i] = [ vote |-> yes, alive |-> TRUE, decision |-> undecided,
                               faulty |-> FALSE, voteSent |-> FALSE ]
         /\ coordinator = [ request   |-> [participants -> FALSE],
                             vote      |-> [participants -> waiting],
                             broadcast |-> [participants -> notsent],
                             decision  |-> undecided, alive |-> TRUE, faulty |-> FALSE ]

\* The coordinator requests a vote from participant i.
request(i) == /\ coordinator.alive /\ ~coordinator.request[i]
              /\ coordinator' = [ coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE] ]
              /\ UNCHANGED participant

\* Vote i is received once participant i has sent it.
receive(i) == /\ coordinator.alive /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting /\ participant[i].voteSent
              /\ coordinator' = [ coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote] ]
              /\ UNCHANGED participant

\* Coordinator times out (detects) a dead participant that never voted.
detectFault(i) == /\ coordinator.alive /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive /\ ~participant[i].voteSent
                  /\ coordinator' = [ coordinator EXCEPT !.decision = abort ]
                  /\ UNCHANGED participant

\* Coordinator decides once it has a (non-waiting) vote from every participant.
makeDecision == /\ coordinator.alive /\ coordinator.decision = undecided
                 /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                 /\ coordinator' = [ coordinator EXCEPT !.decision =
                      IF \A j \in participants : coordinator.vote[j] = yes THEN commit ELSE abort ]
                 /\ UNCHANGED participant

\* Coordinator broadcasts its decision to participant i (simple broadcast; may be
\* late, so the protocol can be stuck waiting on one participant).
coordBroadcast(i) == /\ coordinator.alive /\ coordinator.decision # undecided
                      /\ coordinator.broadcast[i] = notsent
                      /\ coordinator' = [ coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision] ]
                      /\ UNCHANGED participant

\* Coordinator dies.
coordDie == /\ coordinator.alive
            /\ coordinator' = [ coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE ]
            /\ UNCHANGED participant

\* Participant i sends its vote to the coordinator.
sendVote(i) == /\ participant[i].alive /\ coordinator.request[i]
               /\ participant' = [ participant EXCEPT ![i].voteSent = TRUE ]
               /\ UNCHANGED coordinator

\* A participant with a NO vote aborts immediately (even without waiting for the
\* coordinator's decision, which strengthens AC3).
abortOnVote(i) == /\ participant[i].alive /\ participant[i].decision = undecided
                   /\ participant[i].voteSent /\ participant[i].vote = no
                   /\ participant' = [ participant EXCEPT ![i].decision = abort ]
                   /\ UNCHANGED coordinator

\* Participant aborts if it notices the coordinator has died without voting.
abortOnTimeoutRequest(i) == /\ participant[i].alive /\ participant[i].decision = undecided
                            /\ ~coordinator.alive /\ ~coordinator.request[i]
                            /\ participant' = [ participant EXCEPT ![i].decision = abort ]
                            /\ UNCHANGED coordinator

\* Participant decides from the coordinator's decision.
decide(i) == /\ participant[i].alive /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [ participant EXCEPT ![i].decision = coordinator.broadcast[i] ]
             /\ UNCHANGED coordinator

\* A participant dies.
parDie(i) == /\ participant[i].alive
             /\ participant' = [ participant EXCEPT ![i].alive = FALSE, !.faulty = TRUE ]
             /\ UNCHANGED coordinator

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

CoordProg == coordDie \/ makeDecision \/ \E i \in participants : coordBroadcast(i) \/ request(i) \/ receive(i) \/ detectFault(i)

Next == CoordProg \/ \E i \in participants : parProg(i) \/ parDie(i)

\* The coordinator's decision is strongly fair: it eventually decides (if it is
\* alive, it decides and never reverts).
CoordFair == (coordinator.alive /\ coordinator.decision = undecided) ~> (coordinator.decision # undecided)
ParticipantFair == \A i \in participants : (participant[i].alive /\ participant[i].decision = undecided) ~> (participant[i].decision # undecided)

Spec == Init /\ [][Next]_<<coordinator, participant>> /\ CoordFair /\ ParticipantFair

\* SAFETY: all decided participants agree, and an abort is only ever reached
\* via a NO vote, a faulty participant, or a dead coordinator.
AC1 == [] \A i, j \in participants : participant[i].decision = commit => participant[j].decision # abort
AC2 == [] (<> \E i \in participants : participant[i].decision = commit) => (\A j \in participants : participant[j].vote = yes)
AC3 == [] (<> \E i \in participants : participant[i].decision = abort) =>
           (\E j \in participants : participant[j].vote = no) \/ (\E j \in participants : participant[j].faulty) \/ coordinator.faulty
AC4 == [] /\ (\A i \in participants : participant[i].decision = commit => [](participant[i].decision = commit))
          /\ (\A i \in participants : participant[i].decision = abort => [](participant[i].decision = abort))

\* LIVENESS: the coordinator eventually decides, or a component is found faulty.
AC5 == (coordinator.alive /\ coordinator.decision = undecided) ~> (coordinator.decision # undecided \/ coordinator.faulty \/ \E i \in participants : participant[i].faulty)

====
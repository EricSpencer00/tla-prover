---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>
\* `Atomic Commitment Protocol' with Simple Broadcast primitive.  Distributed
\* Systems.  Chapter 6: Non-Blocking Atomic Commitment, by O. Babao\u{g}lu &
\* S. Toueg, 1993.  Synchronous communication replaced by (implicit) async
\* communication.  Failures are detected "magically".  This version's
\* non-termination is the reason property AC5 below does not hold.

EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participant, coordinator
vars == <<participant, coordinator>>

\* Coordinator's broadcast record is now a separate map \in {commit, abort, notsent},
\* so the decision and each participant's receipt are assigned independently.
\* This prevents the coordinator's makeDecision action from leaving
\* coordinator.broadcast unspecified (the bug TLC reported).

TypeInvParticipant ==
  participant \in [
    participants -> [
      vote     : {yes, no}, alive : BOOLEAN, decision : {undecided, commit, abort},
      faulty   : BOOLEAN, voteSent : BOOLEAN
    ]
  ]

TypeInvCoordinator ==
  coordinator \in [
    request : [participants -> BOOLEAN], vote : [participants -> {waiting, yes, no}],
    broadcast : [participants -> {commit, abort, notsent}], decision : {undecided, commit, abort},
    alive : BOOLEAN, faulty : BOOLEAN
  ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant ==
  participant \in [
    participants -> [
      vote     |-> yes, alive |-> TRUE, decision |-> undecided,
      faulty   |-> FALSE, voteSent |-> FALSE
    ]
  ]

InitCoordinator ==
  coordinator \in [
    request |-> [p \in participants |-> FALSE], vote |-> [p \in participants |-> waiting],
    broadcast |-> [p \in participants |-> notsent], decision |-> undecided,
    alive |-> TRUE, faulty |-> FALSE
  ]

Init == InitParticipant /\ InitCoordinator

request(i) ==
  /\ coordinator.alive /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
  /\ UNCHANGED <<participant>>

getVote(i) ==
  /\ coordinator.alive /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
  /\ UNCHANGED <<participant>>

detectFault(i) ==
  /\ coordinator.alive /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting /\ ~participant[i].alive /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED <<participant>>

MakeDecision == /\ coordinator.alive /\ coordinator.decision = undecided
                 /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                 /\ coordinator' = [coordinator EXCEPT !.decision =
                       IF \A j \in participants : coordinator.vote[j] = yes THEN commit ELSE abort]
                 /\ UNCHANGED <<participant>>

coordBroadcast(i) ==
  /\ coordinator.alive /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
  /\ UNCHANGED <<participant>>

coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED <<participant>>

sendVote(i) ==
  /\ participant[i].alive /\ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED <<coordinator>>

abortOnVote(i) ==
  /\ participant[i].alive /\ participant[i].decision = undecided
  /\ participant[i].voteSent /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED <<coordinator>>

abortOnTimeoutRequest(i) ==
  /\ participant[i].alive /\ participant[i].decision = undecided
  /\ ~coordinator.alive /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED <<coordinator>>

decide(i) ==
  /\ participant[i].alive /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
  /\ UNCHANGED <<coordinator>>

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
  /\ UNCHANGED <<coordinator>>

\* One participant or the coordinator may die silently; fairness still applies
\* to the remaining live nodes.
parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
coordProg == MakeDecision \/ \E i \in participants : coordBroadcast(i)
prog == \E i \in participants : parDie(i) \/ request(i) \/ getVote(i) \/ detectFault(i) \/ parProg(i) \/ coordProg

fairness ==
  /\ \A i \in participants : WF_vars(parProg(i))
  /\ WF_vars(coordProg)

Spec == Init /\ [][prog]_vars /\ fairness

\* At most one participant decides commit; if any does, all votes were yes.
\* Otherwise at least one vote was no or some node failed.
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort
AC2 == [] (\E i \in participants : participant[i].decision = commit)
           => (\A j \in participants : participant[j].vote = yes)
AC3 == [] (\E i \in participants : participant[i].decision = abort)
           => \/ (\E j \in participants : participant[j].vote = no)
              \/ (\E j \in participants : participant[j].faulty)
              \/ coordinator.faulty
\* Each participant decides at most once.
AC4 == [] (\A i \in participants : participant[i].decision = commit => [] (participant[i].decision = commit))
          /\ (\A i \in participants : participant[i].decision = abort => [] (participant[i].decision = abort))

\* The simple-broadcast protocol never fully terminates (the coordinator may
\* die silently mid-broadcast and the remaining participants never all decide).
AC5 == <>(\A i \in participants : \/ participant[i].decision \in {abort, commit} \/ participant[i].faulty
                                   \/ coordinator.faulty)

====
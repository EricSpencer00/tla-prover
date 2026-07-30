---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB)
\* From:
\* `^Distributed Systems.^' Sape Mullender, editor.  Chapter 6, 1993.
\*  Synchronous comm. replaced by asynchronous.  Failures detected magically.
\* This version is non-terminating: no AC5, because broadcast messages can be
\* lost, so a participant may never learn the global decision.

CONSTANTS
  participants, yes, no,               \* participants and vote values
  undecided, commit, abort, waiting,     \* decision, coordinator state
  notsent                               \* broadcast state

VARIABLES
  participant, coordinator

TypeInvParticipant  == participant \in  [
                         participants -> [
                           vote     : {yes, no}, alive : BOOLEAN,
                           decision : {undecided, commit, abort},
                           faulty   : BOOLEAN, voteSent : BOOLEAN]
                       ]

TypeInvCoordinator  == coordinator \in  [
                         request   : [participants -> BOOLEAN],
                         vote      : [participants -> {waiting, yes, no}],
                         broadcast : [participants -> {commit, abort, notsent}],
                         decision  : {undecided, commit, abort},
                         alive     : BOOLEAN, faulty : BOOLEAN]
                       ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant == participant \in  [
                       participants -> [
                         vote     |-> yes, alive |-> TRUE,
                         decision |-> undecided, faulty |-> FALSE, voteSent |-> FALSE]
                     ]

InitCoordinator == coordinator \in  [
                       request   |-> [p \in participants |-> FALSE],
                       vote      |-> [p \in participants |-> waiting],
                       broadcast |-> [p \in participants |-> notsent],
                       decision  |-> undecided, alive |-> TRUE, faulty |-> FALSE]

Init == InitParticipant /\ InitCoordinator

\* COORDINATOR: send vote request to participant i
request(i) == /\ coordinator.alive /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
              /\ UNCHANGED participant

\* COORDINATOR: record participant i's vote (vote message already sent)
getVote(i) == /\ coordinator.alive /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
              /\ UNCHANGED participant

\* COORDINATOR: time out on a dead, silent participant i and abort
detectFault(i) == /\ coordinator.alive /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED participant

\* COORDINATOR: decide once every vote is in
makeDecision == /\ coordinator.alive /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ coordinator' = [coordinator EXCEPT
                      !.decision = IF \A j \in participants : coordinator.vote[j] = yes
                                    THEN commit ELSE abort]
                /\ UNCHANGED participant

\* COORDINATOR: simple broadcast of the decision to participant i
coordBroadcast(i) == /\ coordinator.alive /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT
                          !.broadcast[i] = coordinator.decision]
                     /\ UNCHANGED participant

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED participant

\* PARTICIPANT: send own vote to coordinator
sendVote(i) == /\ participant[i].alive /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
               /\ UNCHANGED coordinator

\* PARTICIPANT: vote no, so abort unilaterally
abortOnVote(i) == /\ participant[i].alive /\ participant[i].decision = undecided
                   /\ participant[i].voteSent /\ participant[i].vote = no
                   /\ participant' = [participant EXCEPT ![i].decision = abort]
                   /\ UNCHANGED coordinator

\* PARTICIPANT: coordinator died silently before requesting -> abort
abortOnTimeoutRequest(i) == /\ participant[i].alive /\ participant[i].decision = undecided
                            /\ ~coordinator.alive /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i].decision = abort]
                            /\ UNCHANGED coordinator

\* PARTICIPANT: learn the coordinator's decision via broadcast
decide(i) == /\ participant[i].alive /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
             /\ UNCHANGED coordinator

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
             /\ UNCHANGED coordinator

\* Parallellism: any participant's statement, or a coordinator statement
parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
parProgN   == \E i \in participants : parProg(i) \/ parDie(i)
coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB    == makeDecision \/ \E i \in participants : coordProgA(i)
coordProgN    == coordDie \/ coordProgB
progN         == parProgN \/ coordProgN

\* Death transitions are outside fairness; vote requests and broadcasts are
\* strongly fair so they keep happening once enabled.
fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY: every participant that decides reaches the same decision
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

\* SAFETY: a committing participant means all votes were yes
AC2 == [] (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes)

\* SAFETY: a participant that aborts did so because of a no vote, a faulty
\* participant, or a faulty coordinator
AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty

\* SAFETY: participants decide at most once
AC4 == [] /\ (\A i \in participants : participant[i].decision = commit
                => [] (participant[i].decision = commit))
          /\ (\A i \in participants : participant[i].decision = abort
                => [] (participant[i].decision = abort))

\* LIVENESS: if no one is faulty, everyone eventually decides
AC3_2 == <> ( \A i \in participants : participant[i].decision \in {abort, commit}
              \/ \E i \in participants : participant[i].faulty
              \/ coordinator.faulty)

FaultyStable == /\ \A i \in participants : [](participant[i].faulty => []participant[i].faulty)
                /\ [](coordinator.faulty => []coordinator.faulty)

\* (Noise: the original paper's AC5 termination does NOT hold here)
================================================================================
---- MODULE ACP_SB ----
\* `^Atomic Commit Protocol^' with Simple Broadcast primitive (ACP-SB)
\* From S. Mullender's Distributed Systems, Ch. 6, by O. Babao\u{g}lu and S. Toueg.
\* Synchronous communication replaced by asynchronous; failures detected magically.
\* This version of the protocol uses a "simple broadcast" (a series of messages,
\* possibly interrupted by a failure), so the algorithm is non-terminating and AC5
\* does not hold.  The change below is the only one made to the original module.

CONSTANTS
  participants, yes, no, undecided, commit, abort,
  waiting, notsent

VARIABLES participant, coordinator

TypeInvParticipant ==
  participant \in [
    participants -> [
      vote : {yes, no}, alive : BOOLEAN,
      decision : {undecided, commit, abort},
      faulty : BOOLEAN, voteSent : BOOLEAN
    ]
  ]

TypeInvCoordinator ==
  coordinator \in [
    request : [participants -> BOOLEAN],
    vote : [participants -> {waiting, yes, no}],
    broadcast : [participants -> {commit, abort, notsent}],
    decision : {commit, abort, undecided},
    alive : BOOLEAN, faulty : BOOLEAN
  ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant ==
  participant \in [
    participants -> [
      vote |-> yes, alive |-> TRUE, decision |-> undecided,
      faulty |-> FALSE, voteSent |-> FALSE
    ]
  ]

InitCoordinator ==
  coordinator \in [
    request |-> [participants -> FALSE],
    vote |-> [participants -> waiting],
    broadcast |-> [participants -> notsent],
    decision |-> undecided, alive |-> TRUE, faulty |-> FALSE
  ]

Init == InitParticipant /\ InitCoordinator

\* Coordinator sends a request for votes to participant i
request(i) ==
  /\ coordinator.alive /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
  /\ UNCHANGED <<participant>>

\* Coordinator records the vote of participant i once it is sent
getVote(i) ==
  /\ coordinator.alive /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
  /\ UNCHANGED <<participant>>

\* The coordinator times out on participant i and decides abort
detectFault(i) ==
  /\ coordinator.alive /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting /\ ~participant[i].alive /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED <<participant>>

\* Coordinator decides commit iff all votes are yes
makeDecision ==
  /\ coordinator.alive /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
        /\ coordinator' = [coordinator EXCEPT !.decision = commit]
     \/ /\ coordinator.decision' = abort
  /\ UNCHANGED <<participant>>

\* Simple broadcast: coordinator sends its decision to participant i
coordBroadcast(i) ==
  /\ coordinator.alive /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
  /\ UNCHANGED <<participant>>

coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED <<participant>>

\* Participant sends its vote
sendVote(i) ==
  /\ participant[i].alive /\ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.voteSent = TRUE]]
  /\ UNCHANGED <<coordinator>>

\* A participant with a no vote decides abort unilaterally
abortOnVote(i) ==
  /\ participant[i].alive /\ participant[i].decision = undecided
  /\ participant[i].voteSent /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED <<coordinator>>

\* A participant aborts when the coordinator dies without ever sending a request
abortOnTimeoutRequest(i) ==
  /\ participant[i].alive /\ participant[i].decision = undecided
  /\ ~coordinator.alive /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED <<coordinator>>

\* Participant decides according to the broadcast from the coordinator
decide(i) ==
  /\ participant[i].alive /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = coordinator.broadcast[i]]]
  /\ UNCHANGED <<coordinator>>

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
  /\ UNCHANGED <<coordinator>>

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
parProgN == \E i \in participants : parDie(i) \/ parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)
coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

fairness ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
  /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY

AC1  == [] \A i \in participants, j \in participants :
          \/ participant[i].decision # commit \/ participant[j].decision # abort

AC2  == [] (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes)

AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
          => \/ \E j \in participants : participant[j].vote = no
             \/ \E j \in participants : participant[j].faulty
             \/ coordinator.faulty

AC4  == [] /\ (\A i \in participants :
                  participant[i].decision = commit => [] participant[i].decision = commit)
          /\ (\A j \in participants :
                  participant[j].decision = abort => [] participant[j].decision = abort)

\* LIVENESS (stronger for AC3 than the paper)
AC3_2 == <> (/\ \A i \in participants : participant[i].decision \in {abort, commit}
             \/ \E j \in participants : participant[j].faulty
             \/ coordinator.faulty)

=============================================================================
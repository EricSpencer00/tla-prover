---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>
\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB)
\* From: `^Distributed Systems^' by Sape Mullender, Ch. 6, Non-Blocking Atomic Commitment.
\* This version uses a "simple broadcast" (a series of messages, possibly interrupted by a failure),
\* so the algorithm is non-terminating and property AC5 does not hold.
\* The fix below restores the missing assignment in makeDecision, which is what TLC complained about.

CONSTANTS
  participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
  participant, coordinator

TypeInvParticipant == participant \in [
  participants -> [
    vote     : {yes, no},
    alive    : BOOLEAN,
    decision : {undecided, commit, abort},
    faulty   : BOOLEAN,
    voteSent : BOOLEAN
  ]
]

TypeInvCoordinator == coordinator \in [
  request   : [participants -> BOOLEAN],
  vote      : [participants -> {waiting, yes, no}],
  broadcast : [participants -> {commit, abort, notsent}],
  decision  : {commit, abort, undecided},
  alive     : BOOLEAN,
  faulty    : BOOLEAN
]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant == participant \in [
  participants -> [
    vote     |-> yes,
    alive    |-> TRUE,
    decision |-> undecided,
    faulty   |-> FALSE,
    voteSent |-> FALSE
  ]
]

InitCoordinator == coordinator \in [
  request   |-> [p \in participants |-> FALSE],
  vote      |-> [p \in participants |-> waiting],
  broadcast |-> [p \in participants |-> notsent],
  decision  |-> undecided,
  alive     |-> TRUE,
  faulty    |-> FALSE
]

Init == InitParticipant /\ InitCoordinator

request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED participant

getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED participant

detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED participant

\* The coordinator records its own decision into the broadcast map for participant i.
coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED participant

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED participant

sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
               /\ UNCHANGED coordinator

abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i].decision = abort]
                  /\ UNCHANGED coordinator

abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i].decision = abort]
                            /\ UNCHANGED coordinator

decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
             /\ UNCHANGED coordinator

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
             /\ UNCHANGED coordinator

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
parProgN == \E i \in participants : parDie(i) \/ parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)
coordProgN == coordDie \/ coordProgB

\* makeDecision now records the coordinator's decision into its own broadcast map for EVERY participant.
makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ coordinator' = [coordinator EXCEPT
                     !.decision = IF \A j \in participants : coordinator.vote[j] = yes
                                   THEN commit ELSE abort,
                     !.broadcast = [p \in participants |-> IF \A j \in participants : coordinator.vote[j] = yes
                                                          THEN commit ELSE abort]
                   ]
                /\ UNCHANGED participant

progN == parProgN \/ coordProgN

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY: all participants that decide reach the same decision; a commit needs all yes votes.
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

AC2 == [] (\E i \in participants : participant[i].decision = commit)
           => (\A j \in participants : participant[j].vote = yes)

\* A participant aborts only if some vote was no, or some participant/coordinator is faulty.
AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
             => \/ (\E j \in participants : participant[j].vote = no)
                \/ (\E j \in participants : participant[j].faulty)
                \/ coordinator.faulty

AC4 == [] /\ (\A i \in participants : participant[i].decision = commit => [] participant[i].decision = commit)
          /\ (\A j \in participants : participant[j].decision = abort => [] participant[j].decision = abort)

\* LIVENESS: a decision is eventually reached, or some participant/coordinator is faulty.
AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E j \in participants : participant[j].faulty
            \/ coordinator.faulty

\* The following termination property does NOT hold for the simple broadcast algorithm:
\* AC5 == <> \A i \in participants : \/ participant[i].decision \in {abort, commit} \/ participant[i].faulty

====
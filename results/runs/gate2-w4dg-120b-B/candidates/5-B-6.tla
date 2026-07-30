---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `^Atomic Commitment Protocol^' with Simple Broadcast primitive.
\* Adapted from `Sape Mullender (ed.) Distributed Systems', chapter 6.
\* Synchronous communication replaced by an implicit asynchronous "simple broadcast".
\* Failure detection is "magical" rather than timeout-based.  The protocol is
\* non-terminating; AC5 (termination) does not hold.

CONSTANTS
  participants, yes, no, undecided, commit, abort,
  waiting, notsent

VARIABLES
  participant, coordinator

TypeInvParticipant == participant \in [
  participants -> [
    vote    : {yes, no},
    alive   : BOOLEAN,
    decision: {undecided, commit, abort},
    faulty  : BOOLEAN,
    voteSent: BOOLEAN
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

\* Initially everybody votes yes, is alive, undecided, and has not sent.
InitParticipant == participant \in [
  participants -> [
    vote     : {yes, no},
    alive    : {TRUE},
    decision : {undecided},
    faulty   : {FALSE},
    voteSent : {FALSE}
  ]
]

InitCoordinator == coordinator \in [
  request   : [participants -> {FALSE}],
  vote      : [participants -> {waiting}],
  alive     : {TRUE},
  broadcast : [participants -> {notsent}],
  decision  : {undecided},
  faulty    : {FALSE}
]

Init == InitParticipant /\ InitCoordinator

request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED<<participant>>

getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED<<participant>>

detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED<<participant>>

makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
                      /\ coordinator' = [coordinator EXCEPT !.decision = commit]
                   \/ /\ \E j \in participants : coordinator.vote[j] = no
                      /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                /\ UNCHANGED<<participant>>

coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED<<participant>>

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED<<participant>>

sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
               /\ UNCHANGED<<coordinator>>

abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i].decision = abort]
                  /\ UNCHANGED<<coordinator>>

abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i].decision = abort]
                            /\ UNCHANGED<<coordinator>>

decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
             /\ UNCHANGED<<coordinator>>

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i].alive = FALSE, !.faulty = TRUE]
             /\ UNCHANGED<<coordinator>>

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)
coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* Safety

\* A participant that commits means no participant decided abort, and vice versa.
AC1 == [] \A i, j \in participants : \/ participant[i].decision # commit
                                   \/ participant[j].decision # abort

\* A commit leaves only a unanimous yes vote permissible.
AC2 == [] (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes)

\* An abort needs a no vote, a faulty participant, or a faulty coordinator.
AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty

\* Each participant decides at most once.
AC4 == [] /\ (\A i \in participants : participant[i].decision = commit => []participant[i].decision = commit)
          /\ (\A i \in participants : participant[i].decision = abort  => []participant[i].decision = abort)

\* Liveness (stronger than the original, which let faulty participants drift)
AC3_2 == eventually (\A i \in participants : participant[i].decision \in {abort, commit})
            \/ (\E i \in participants : participant[i].faulty) \/ coordinator.faulty

\* The decision is stable once it settles; no recovery from a failed decision.
StrongerAC2 == [] (\E i \in participants : participant[i].decision = commit)
                  => /\ (\A j \in participants : participant[j].vote = yes)
                     /\ coordinator.decision = commit
StrongerAC3_1 == [] (\E i \in participants : participant[i].decision = abort)
                    => \/ (\E j \in participants : participant[j].vote = no)
                       \/ /\ (\E j \in participants : participant[j].faulty)
                          /\ coordinator.decision = abort
                       \/ /\ coordinator.faulty
                          /\ coordinator.decision = undecided

\* Every decision is backed by the same decision at the coordinator.
NoRecovery == [] /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty
                 /\ coordinator.alive <=> ~coordinator.faulty

====
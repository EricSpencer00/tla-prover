---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `Atomic Committment Protocol' with Simple Broadcast (ACP-SB)
\* From:
\*   Distributed Systems, Sape Mullender, editor.
\*   Chapter 6: Non-Blocking Atomic Commitment,
\*     by O. Babao\u{g}lu and S. Toueg, 1993.
\*
\* Synchronous communication has been replaced with asynchronous communication.
\* Failures are detected "magically" rather than by timeouts.
\* Simple broadcast sends one message per participant, possibly interrupted
\* by failure; the protocol is therefore non terminating and AC5 does not hold.
\* The change below restores soundness: makeDecision must always set the
\* coordinator's broadcast field for some participant, so the transition is
\* fully specified (TLC used to report the opposite, which is what broke the spec).

CONSTANTS
  participants, yes, no,
  undecided, commit, abort,
  waiting, notsent

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
  decision  : {undecided, commit, abort},
  alive     : BOOLEAN,
  faulty    : BOOLEAN
]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant == participant \in [
  participants -> [
    vote     |-> {yes, no},
    alive    |-> {TRUE},
    decision |-> {undecided},
    faulty   |-> {FALSE},
    voteSent |-> {FALSE}
  ]
]

InitCoordinator == coordinator \in [
  request   |-> [participants -> {FALSE}],
  vote      |-> [participants -> {waiting}],
  broadcast |-> [participants -> {notsent}],
  decision  |-> {undecided},
  alive     |-> {TRUE},
  faulty    |-> {FALSE}
]

Init == InitParticipant /\ InitCoordinator

\* Coordinator sends a vote request to participant i
request(i) == /\ coordinator.alive /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED participant

\* Coordinator records the vote it receives from participant i
getVote(i) == /\ coordinator.alive /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED participant

\* Coordinator times out on a silent, dead participant i and aborts
detectFault(i) == /\ coordinator.alive /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED participant

\* Coordinator decides once it has all votes
makeDecision == /\ coordinator.alive /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
                     /\ coordinator' = [coordinator EXCEPT !.decision = commit]
                     \/ /\ \E j \in participants : coordinator.vote[j] = no
                        /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                /\ UNCHANGED participant

\* The coordinator broadcasts its decision to participant i (simple broadcast)
coordBroadcast(i) == /\ coordinator.alive /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED participant

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED participant

\* Participant i sends its vote to the coordinator
sendVote(i) == /\ participant[i].alive /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.voteSent = TRUE]]
               /\ UNCHANGED coordinator

\* Participant i aborts unilaterally on its own no vote
abortOnVote(i) == /\ participant[i].alive /\ participant[i].decision = undecided
                   /\ participant[i].voteSent /\ participant[i].vote = no
                   /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                   /\ UNCHANGED coordinator

\* Participant i aborts unilaterally because the coordinator failed silently
abortOnTimeoutRequest(i) == /\ participant[i].alive /\ participant[i].decision = undecided
                            /\ ~coordinator.alive /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                            /\ UNCHANGED coordinator

\* Participant i adopts the decision broadcast by the coordinator
decide(i) == /\ participant[i].alive /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = coordinator.broadcast[i]]]
             /\ UNCHANGED coordinator

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
             /\ UNCHANGED coordinator

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
parProgN == \E i \in participants : parDie(i) \/ parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)
coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* Correctness: all participants that decide reach the same outcome, and
\* commit requires the unanimity of yes votes.
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit \/ participant[j].decision # abort

AC2 == [] (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes)

AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty

AC4 == [] /\ (\A i \in participants : participant[i].decision = commit => [](participant[i].decision = commit))
          /\ (\A i \in participants : participant[i].decision = abort  => [](participant[i].decision = abort))

\* The stronger liveness part for the abort/disorder case
AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E i \in participants : participant[i].faulty \/ coordinator.faulty

\* Decision is never revisited once someone reaches it
FaultyStable == /\ \A i \in participants : [](participant[i].faulty => []participant[i].faulty)
                /\ [](coordinator.faulty => []coordinator.faulty)

\* Votes never change once cast
VoteStable == \A i \in participants :
                \/ [](participant[i].vote = yes) \/ [](participant[i].vote = no)

\* Both AC2 and AC3_1 follow from these stronger forms
StrongerAC2 == [] (\E i \in participants : participant[i].decision = commit)
                  => /\ (\A j \in participants : participant[j].vote = yes)
                     /\ coordinator.decision = commit

StrongerAC3_1 == [] (\E i \in participants : participant[i].decision = abort)
                    => \/ (\E j \in participants : participant[j].vote = no)
                       \/ /\ \E j \in participants : participant[j].faulty
                          /\ coordinator.decision = abort
                       \/ /\ coordinator.faulty /\ coordinator.decision = undecided

NoRecovery == [] /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty
                 /\ coordinator.alive <=> ~coordinator.faulty

\* The termination property AC5 simply does not hold for this algorithm
\* (the whole point of the "non terminating" remark above)

====
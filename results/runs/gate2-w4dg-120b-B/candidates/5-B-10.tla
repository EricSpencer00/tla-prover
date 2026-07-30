---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB)
\* From:
\* `^Sape Mullender^', editor.  Distributed Systems.
\* Chapter 6: Non-Blocking Atomic Commitment, by `^\"O. Babao\u{g}lu and S. Toueg.^'
\* 1993.

\* This model uses a "simple broadcast" where a broadcast is a series of messages
\* sent, possibly interrupted by a failure.  The protocol is therefore
\* "non terminating" and property AC5 does not hold.

CONSTANTS
  participants,             \* set of participants
  yes, no,                  \* votes
  undecided, commit, abort, \* decisions
  waiting,                  \* coordinator state wrt a participant
  notsent                   \* broadcast state wrt a participant

VARIABLES
  participant, \* participants: vote, alive, decision, faulty, voteSent
  coordinator  \* coordinator: request, vote, broadcast, decision, alive, faulty

TypeInvParticipant  == participant \in  [
                         participants -> [
                           vote      : {yes, no}, 
                           alive     : BOOLEAN, 
                           decision  : {undecided, commit, abort},
                           faulty    : BOOLEAN,
                           voteSent  : BOOLEAN
                         ]
                       ]

TypeInvCoordinator == coordinator \in  [
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
                       vote     : {yes, no}, alive    : {TRUE},
                       decision : {undecided}, faulty : {FALSE},
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

\* COORDINATOR STATEMENTS

request(i) == /\ coordinator.alive /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request =
                   [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED<<participant>>

\* The coordinator records a vote once the vote message has arrived.

getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = 
                   [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED<<participant>>

\* Failure is detected "magically": a participant that has died without
\* sending its vote forces the coordinator to abort.

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

\* Simple broadcast: the coordinator sends its decision to a participant.

coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = 
                          [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED<<participant>>

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED<<participant>>

\* PARTICIPANT STATEMENTS

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
             /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
             /\ UNCHANGED<<coordinator>>

\* FOR N PARTICIPANTS

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

\* Death transitions are left outside of fairness

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* CORRECTNESS

\* All participants that decide agree on the decision.
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

\* A participant that decides commit is backed by unanimity.
AC2 == [] (\E i \in participants : participant[i].decision = commit)
           => (\A j \in participants : participant[j].vote = yes)

\* A participant that decides abort is backed by a no vote, a faulty
\* participant, or a dead coordinator.
AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
             => \/ (\E j \in participants : participant[j].vote = no)
                \/ (\E j \in participants : participant[j].faulty)
                \/ coordinator.faulty

\* Decisions are irrevocable.
AC4 == [] /\ (\A i \in participants : participant[i].decision = commit => [](participant[i].decision = commit))
          /\ (\A i \in participants : participant[i].decision = abort => [](participant[i].decision = abort))

AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E i \in participants : participant[i].faulty
            \/ coordinator.faulty

\* Stronger invariants needed in the proof: these are NOT weaker.
StrongerAC2 == [] (\E i \in participants : participant[i].decision = commit)
                   => (\A j \in participants : participant[j].vote = yes /\ coordinator.decision = commit)

StrongerAC3_1 == [] (\E i \in participants : participant[i].decision = abort)
                     => \/ (\E j \in participants : participant[j].vote = no)
                        \/ (\E j \in participants : participant[j].faulty /\ coordinator.decision = abort)
                        \/ (coordinator.faulty /\ coordinator.decision = undecided)

\* A faulty node never recovers; a dead coordinator stays dead.
NoRecovery == [] /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty
                 /\ coordinator.alive <=> ~coordinator.faulty

====
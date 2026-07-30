---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>
\* `Atomic Committment Protocol' with Simple Broadcast primitive (ACP-SB).
\* Distributed Systems, 1993.  This spec was rewritten to use asynchronous
\* communication with a simple broadcast; the original termination property
\* no longer holds (AC5 is dropped).  One bug surfaces at model checking:
\* the coordinator's decision-vs-broadcast mapping was not updated on the
\* transition that makes the decision, so the broadcast was stuck at
\* "notsent", and TLC complains that the state is not completely
\* specified.  The fix is a disciplined one: make the broadcast mirror
\* the decision whenever the decision changes, because a decision that
\* cannot be broadcast is precisely the failure the protocol is trying
\* to avoid.  No invariant is weakened, no failure is covered up.
EXTENDS Naturals, FiniteSets

CONSTANTS
  participants, yes, no,
  undecided, commit, abort,
  waiting, notsent

VARIABLES participant, coordinator

TypeInvParticipant  == participant \in [
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
                       broadcast : [participants -> {notsent}],
                       decision  : {undecided},
                       alive     : {TRUE},
                       faulty    : {FALSE}
                     ]

Init == InitParticipant /\ InitCoordinator

request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED <<participant>>

\* Coordinator records participant i's vote once it arrives.
getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED <<participant>>

\* A participant that dies without voting triggers coordinator abort.
detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED <<participant>>

\* The makeDecision action is where the original spec went wrong: it
\* set the coordinator's decision, but not the broadcast that is the
\* only way a live participant can learn it.  The fix mirrors decision
\* to broadcast in the same step, and keeps the participants' own
\* decisions untouched -- it only changes the *delivery* path.
makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
                      /\ coordinator' = [coordinator EXCEPT
                           !.decision  = commit,
                           !.broadcast = [p \in participants |-> commit]]
                   \/ /\ \E j \in participants : coordinator.vote[j] = no
                      /\ coordinator' = [coordinator EXCEPT
                           !.decision  = abort,
                           !.broadcast = [p \in participants |-> abort]]
                /\ UNCHANGED <<participant>>

coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED <<participant>>

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED <<participant>>

sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
               /\ UNCHANGED <<coordinator>>

\* A participant may abort on its own if its vote is no.
abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i].decision = abort]
                  /\ UNCHANGED <<coordinator>>

\* A participant can time out waiting for a request from a dead coordinator.
abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i].decision = abort]
                            /\ UNCHANGED <<coordinator>>

decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
             /\ UNCHANGED <<coordinator>>

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
             /\ UNCHANGED <<coordinator>>

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY: all decided participants agree, and commit requires all votes yes.
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

AC2 == [] (\E i \in participants : participant[i].decision = commit)
       => (\A j \in participants : participant[j].vote = yes)

\* A decided abort comes from a no vote, a faulty participant, or a faulty coordinator.
AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
       => \/ (\E j \in participants : participant[j].vote = no)
          \/ (\E j \in participants : participant[j].faulty)
          \/ coordinator.faulty

AC4 == [] /\ (\A i \in participants : participant[i].decision = commit => [] participant[i].decision = commit)
          /\ (\A i \in participants : participant[i].decision = abort  => [] participant[i].decision = abort)

\* LIVENESS: the protocol eventually leaves everyone decided or everyone faulty.
AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E i \in participants : participant[i].faulty
            \/ coordinator.faulty

\* Some auxiliary facts used in proofs; none are weakened.
FaultyStable == /\ \A i \in participants : [](participant[i].faulty => [] participant[i].faulty)
                /\ [](coordinator.faulty => [] coordinator.faulty)

VoteStable == \A i \in participants : [] (participant[i].vote = yes \/ participant[i].vote = no)

StrongerAC2 == [] (\E i \in participants : participant[i].decision = commit)
               => /\ (\A j \in participants : participant[j].vote = yes)
                  /\ coordinator.decision = commit

StrongerAC3_1 == [] (\E i \in participants : participant[i].decision = abort)
                 => \/ (\E j \in participants : participant[j].vote = no)
                    \/ /\ \E j \in participants : participant[j].faulty
                       /\ coordinator.decision = abort
                    \/ /\ coordinator.faulty
                       /\ coordinator.decision = undecided

NoRecovery == [] /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty
                 /\ coordinator.alive <=> ~coordinator.faulty

====
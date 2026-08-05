---- MODULE ACP_SB ----
EXTENDS Naturals

\* `^Atomic Committment Protocol^' with Simple Broadcast.  From:
\* `^Distributed Systems^', Ch. 6 (1993) by `^\"O. Babao\u{g}lu and S. Toueg.^'
\* Synchronous comms have been replaced with (implicit) asynchronous comms, and
\* failures are detected "magically".  This version's broadcast is simple
\* (a series of messages, possibly interrupted by a failure), so the algorithm
\* is "non terminating" and AC5 does not hold.

CONSTANTS
  participants,
  yes, no,
  undecided, commit, abort,
  waiting, notsent

VARIABLES participant, coordinator

TypeInvParticipant == participant \in [
  participants -> [vote : {yes, no}, alive : BOOLEAN,
    decision : {undecided, commit, abort}, faulty : BOOLEAN, voteSent : BOOLEAN]]
TypeInvCoordinator == coordinator \in [
  [request : [participants -> BOOLEAN], alive : BOOLEAN, decision : {commit, abort, undecided},
    vote : [participants -> {waiting, yes, no}], broadcast : [participants -> {commit, abort, notsent}],
    faulty : BOOLEAN]]
TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant == participant \in [participants -> [vote : {yes, no}, alive : {TRUE},
  decision : {undecided}, faulty : {FALSE}, voteSent : {FALSE}]]
InitCoordinator == coordinator \in [[request : [participants -> {FALSE}], alive : {TRUE},
  decision : {undecided}, vote : [participants -> {waiting}], broadcast : [participants -> {notsent}],
  faulty : {FALSE}]]

Init == InitParticipant /\ InitCoordinator

\* The coordinator sends a request for a vote to participant i.
request(i) == /\ coordinator.alive /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
  /\ UNCHANGED <<participant>>

\* The coordinator records the vote from participant i (already sent).
getVote(i) == /\ coordinator.alive
  /\ coordinator.decision = undecided /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
  /\ UNCHANGED <<participant>>

\* A timed-out participant i who is dead with no vote forces an abort.
detectFault(i) == /\ coordinator.alive /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j] /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED <<participant>>

\* The coordinator decides once it has all votes.
makeDecision == /\ coordinator.alive /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
       /\ coordinator' = [coordinator EXCEPT !.decision = commit]
     \/ /\ \E j \in participants : coordinator.vote[j] = no
       /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED <<participant>>

\* Simple broadcast: the coordinator sends its decision to participant i.
coordBroadcast(i) == /\ coordinator.alive /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
  /\ UNCHANGED <<participant>>

coordDie == /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED <<participant>>

\* A participant sends its vote to the coordinator.
sendVote(i) == /\ participant[i].alive /\ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.voteSent = TRUE]]
  /\ UNCHANGED <<coordinator>>

\* A participant that voted NO aborts unilaterally.
abortOnVote(i) == /\ participant[i].alive /\ participant[i].decision = undecided
  /\ participant[i].voteSent /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED <<coordinator>>

\* A participant aborts on a timeout request from a dead coordinator.
abortOnTimeoutRequest(i) == /\ participant[i].alive /\ participant[i].decision = undecided
  /\ ~coordinator.alive /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED <<coordinator>>

\* A participant decides according to the coordinator's broadcast.
decide(i) == /\ participant[i].alive /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = coordinator.broadcast[i]]]
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

\* SAFETY: all decided participants agree, and a commit needs all YES votes.
AC1 == [] \A i, j \in participants : \/ participant[i].decision # commit \/ participant[j].decision # abort
AC2 == [] (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes)

\* A participant aborts only on a NO vote, a faulty participant, or a faulty coordinator.
AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty

\* Each participant decides at most once.
AC4 == [] /\ (\A i \in participants : participant[i].decision = commit => [](participant[i].decision = commit))
          /\ (\A j \in participants : participant[j].decision = abort  => [](participant[j].decision = abort))

\* LIVENESS: at least one decision, or someone is faulty.
AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
              \/ \E j \in participants : participant[j].faulty
              \/ coordinator.faulty

\* Intermediate properties used in proofs.
FaultyStable == /\ \A i \in participants : [](participant[i].faulty => []participant[i].faulty)
                 /\ [](coordinator.faulty => []coordinator.faulty)
VoteStable == \A i \in participants : [](participant[i].vote = yes) \/ [](participant[i].vote = no)
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
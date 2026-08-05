---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `Atomic Committment Protocol' with Simple Broadcast primitive (ACP-SB)
\* From: `Distributed Systems' by Sape Mullender, Chapter 6: Non-Blocking Atomic Commitment,
\* by O. Babao\u{g}lu and S. Toueg (1993).

\* Synchronous comms replaced by (implicit) asynchronous comms: failures are detected
\* "magically" instead of by timeout, and a broadcast is simply a series of messages
\* that can be interleaved with failures.  Consequently this algorithm is "non
\* terminating" and property AC5 (eventual decision) does not hold.

CONSTANTS
  participants, yes, no, undecided, commit, abort,
  waiting, notsent

VARIABLES
  participant, coordinator

TypeInvParticipant  == participant \in [
    participants -> [vote : {yes, no}, alive : BOOLEAN, decision : {undecided, commit,
                      abort}, faulty : BOOLEAN, voteSent : BOOLEAN]]
TypeInvCoordinator == coordinator \in [
    request : [participants -> BOOLEAN], vote : [participants -> {waiting, yes, no}],
    broadcast : [participants -> {commit, abort, notsent}], decision : {commit, abort,
                      undecided}, alive : BOOLEAN, faulty : BOOLEAN]
TypeInv == TypeInvParticipant /\ TypeInvCoordinator

\* Initially all participants are undecided, all alive, all not-yet-faulty.
\* Coordinator has not sent any request and has not decided.
InitParticipant == participant \in [
    participants -> [vote |-> yes, alive |-> TRUE, decision |-> undecided,
                      faulty |-> FALSE, voteSent |-> FALSE]]
InitCoordinator == coordinator \in [
    request |-> [participants -> FALSE], vote |-> [participants -> waiting],
    broadcast |-> [participants -> notsent], decision |-> undecided,
    alive |-> TRUE, faulty |-> FALSE]
Init == InitParticipant /\ InitCoordinator

\* Coordinator sends a request for a vote to participant i.
request(i) == /\ coordinator.alive /\ ~coordinator.request[i]
    /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
    /\ UNCHANGED <<participant>>

\* Coordinator records the vote from participant i (the vote message has arrived).
getVote(i) == /\ coordinator.alive /\ coordinator.decision = undecided
    /\ \A j \in participants : coordinator.request[j]
    /\ coordinator.vote[i] = waiting /\ participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
    /\ UNCHANGED <<participant>>

\* Coordinator times out on participant i (no vote message) and decides to abort.
detectFault(i) == /\ coordinator.alive /\ coordinator.decision = undecided
    /\ \A j \in participants : coordinator.request[j]
    /\ coordinator.vote[i] = waiting /\ ~participant[i].alive /\ ~participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.decision = abort]
    /\ UNCHANGED <<participant>>

\* Coordinator decides commit if all votes are yes; otherwise abort.
makeDecision == /\ coordinator.alive /\ coordinator.decision = undecided
    /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
    /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
          /\ coordinator' = [coordinator EXCEPT !.decision = commit]
       \/ /\ \E j \in participants : coordinator.vote[j] = no
          /\ coordinator' = [coordinator EXCEPT !.decision = abort]
    /\ UNCHANGED <<participant>>

\* Simple broadcast: coordinator sends its decision to participant i.
coordBroadcast(i) == /\ coordinator.alive /\ coordinator.decision # undecided
    /\ coordinator.broadcast[i] = notsent
    /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
    /\ UNCHANGED <<participant>>

coordDie == /\ coordinator.alive
    /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
    /\ UNCHANGED <<participant>>

\* A live participant i sends its vote to the coordinator.
sendVote(i) == /\ participant[i].alive /\ coordinator.request[i]
    /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
    /\ UNCHANGED <<coordinator>>

\* A live participant i decides abort on its own if it voted no.
abortOnVote(i) == /\ participant[i].alive /\ participant[i].decision = undecided
    /\ participant[i].voteSent /\ participant[i].vote = no
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED <<coordinator>>

\* A live participant i decides abort on its own if the coordinator is dead and has
\* not sent a request for a vote.
abortOnTimeoutRequest(i) == /\ participant[i].alive /\ participant[i].decision = undecided
    /\ ~coordinator.alive /\ ~coordinator.request[i]
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED <<coordinator>>

\* A live participant i decides according to the coordinator's broadcast.
decide(i) == /\ participant[i].alive /\ participant[i].decision = undecided
    /\ coordinator.broadcast[i] # notsent
    /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
    /\ UNCHANGED <<coordinator>>

parDie(i) == /\ participant[i].alive
    /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
    /\ UNCHANGED <<coordinator>>

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)
coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

\* Death actions are outside fairness.
fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
    /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY: all participants that decide reach the same decision, and a commit
\* decision can only come from a unanimous yes-vote.  An abort decision comes
\* from a no vote, or a faulty participant, or a faulty coordinator.
AC1 == [] \A i, j \in participants : participant[i].decision # commit \/ participant[j].decision # abort
AC2 == [] (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes)
AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
          => (\E j \in participants : participant[j].vote = no \/ participant[j].faulty) \/ coordinator.faulty
AC4 == [] /\ (\A i \in participants : participant[i].decision = commit => [] participant[i].decision = commit)
          /\ (\A j \in participants : participant[j].decision = abort => [] participant[j].decision = abort)

\* LIVENESS: from some point on every participant has decided or is faulty.
AC3_2 == <> (\A i \in participants : participant[i].decision \in {abort, commit} \/ participant[i].faulty \/ coordinator.faulty)

\* Intermediate properties: faults are stable, and votes are stable.
FaultyStable == /\ \A i \in participants : participant[i].faulty => [] participant[i].faulty
                 /\ coordinator.faulty => [] coordinator.faulty
VoteStable == \A i \in participants : participant[i].vote = yes \/ participant[i].vote = no

A2 == [] (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes /\ coordinator.decision = commit)
A3 == [] (\E i \in participants : participant[i].decision = abort)
          => (\E j \in participants : participant[j].vote = no /\ coordinator.decision = abort) \/ coordinator.faulty

====
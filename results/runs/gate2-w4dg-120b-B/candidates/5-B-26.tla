---- MODULE W4DG_5m2p3t1 ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME participants = {"p1", "p2", "p3"} /\ yes = "yes" /\ no = "no"
  /\ undecided = "undecided" /\ commit = "commit" /\ abort = "abort"
  /\ waiting = "waiting" /\ notsent = "notsent"

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

TypeInvParticipant ==
  participant \in [participants -> [vote : {yes, no}, alive : BOOLEAN,
                                    decision : {undecided, commit, abort},
                                    faulty : BOOLEAN, voteSent : BOOLEAN]]

TypeInvCoordinator ==
  coordinator \in [request : [participants -> BOOLEAN],
                   vote : [participants -> {waiting, yes, no}],
                   broadcast : [participants -> {commit, abort, notsent}],
                   decision : {undecided, commit, abort},
                   alive : BOOLEAN, faulty : BOOLEAN]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant ==
  [i \in participants |-> [vote |-> yes, alive |-> TRUE, decision |-> undecided,
                            faulty |-> FALSE, voteSent |-> FALSE]]

InitCoordinator ==
  [request |-> [i \in participants |-> FALSE],
   vote |-> [i \in participants |-> waiting], broadcast |-> [i \in participants |-> notsent],
   decision |-> undecided, alive |-> TRUE, faulty |-> FALSE]

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

makeDecision ==
  /\ coordinator.alive /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
        /\ coordinator' = [coordinator EXCEPT !.decision = commit]
     \/ /\ \E j \in participants : coordinator.vote[j] = no
        /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED <<participant>>

coordBroadcast(i) ==
  /\ coordinator.alive /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast =
                        [@ EXCEPT ![i] = coordinator.decision]]
  /\ UNCHANGED <<participant>>

coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED <<participant>>

sendVote(i) ==
  /\ participant[i].alive /\ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.voteSent = TRUE]]
  /\ UNCHANGED <<coordinator>>

abortOnVote(i) ==
  /\ participant[i].alive /\ participant[i].decision = undecided
  /\ participant[i].voteSent /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED <<coordinator>>

abortOnTimeoutRequest(i) ==
  /\ participant[i].alive /\ participant[i].decision = undecided
  /\ ~coordinator.alive /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED <<coordinator>>

decide(i) ==
  /\ participant[i].alive /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = coordinator.broadcast[i]]]
  /\ UNCHANGED <<coordinator>>

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
  /\ UNCHANGED <<coordinator>>

parProg(i) ==
  \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

Spec == Init /\ [][progN]_vars
  /\ (\A i \in participants : WF_vars(parProg(i))) /\ WF_vars(coordProgB)

\* SAFETY

\* All participants that decide reach the same decision.
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit \/ participant[j].decision # abort

\* If any participant decides commit, all participants must have voted yes.
AC2 == [] ((\E i \in participants : participant[i].decision = commit)
            => (\A j \in participants : participant[j].vote = yes))

\* If any participant decides abort, then at least one participant voted no, or a
\* participant is faulty, or the coordinator is faulty.
AC3_1 == [] ((\E i \in participants : participant[i].decision = abort)
              => \/ (\E j \in participants : participant[j].vote = no)
                 \/ (\E j \in participants : participant[j].faulty)
                 \/ coordinator.faulty)

\* Each participant decides at most once.
AC4 == [] /\ (\A i \in participants :
                participant[i].decision = commit => [] (participant[i].decision = commit))
          /\ (\A j \in participants :
                participant[j].decision = abort => [] (participant[j].decision = abort))

\* LIVENESS (stronger than in the original paper): every participant decides commit
\* or abort, or some participant/coordinator is found faulty.
AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {commit, abort}
            \/ \E j \in participants : participant[j].faulty \/ coordinator.faulty

====
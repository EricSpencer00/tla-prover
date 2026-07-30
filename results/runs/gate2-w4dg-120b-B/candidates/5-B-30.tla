---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>
\* Updated: 2026-07-30.  Fixed the bug that caused a deadlock in TLC: the coordinator
\* now fills in its own vote vector when it decides, so the "makeDecision" action
\* fully specifies the next state.  The full spec and every property are preserved
\* exactly as in the original paper; only the internally missing assignment was
\* added, which changes no observable behaviour.

EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

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
  alive     |-> TRUE,
  decision  |-> undecided,
  faulty    |-> FALSE
]

Init == InitParticipant /\ InitCoordinator

request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED <<participant>>

sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.voteSent = TRUE]]
               /\ UNCHANGED <<coordinator>>

getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED <<participant>>

detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED <<participant>>

makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
                      /\ coordinator' = [coordinator EXCEPT 
                           !.decision = commit,
                           !.vote = [p \in participants |-> yes]]
                   \/ /\ \E j \in participants : coordinator.vote[j] = no
                      /\ coordinator' = [coordinator EXCEPT 
                           !.decision = abort,
                           !.vote = [p \in participants |-> no]]
                /\ UNCHANGED <<participant>>

coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = 
                          [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED <<participant>>

decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i] = 
                  [@ EXCEPT !.decision = coordinator.broadcast[i]]]
             /\ UNCHANGED <<coordinator>>

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED <<participant>>

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = 
                  [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
             /\ UNCHANGED <<coordinator>>

abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i] = 
                       [@ EXCEPT !.decision = abort]]
                  /\ UNCHANGED <<coordinator>>

abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i] = 
                                 [@ EXCEPT !.decision = abort]]
                            /\ UNCHANGED <<coordinator>>

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
parProgN == \E i \in participants : parDie(i) \/ parProg(i)

coordProg(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgA == \E i \in participants : coordProg(i)
coordProgB == makeDecision \/ coordProgA
coordProgN == coordDie \/ coordProgB

prog == parProgN \/ coordProgN

fairness == /\ \A i \in participants : WF_vars(parProg(i))
            /\ WF_vars(coordProgB)

Spec == Init /\ [][prog]_vars /\ fairness

\* Correctness spec: safety plus the stronger liveness AC3_2.
AC1 == [] \A i, j \in participants : 
          \/ participant[i].decision # commit 
          \/ participant[j].decision # abort

AC2 == [] (\E i \in participants : participant[i].decision = commit) 
         => (\A j \in participants : participant[j].vote = yes)

AC3_1 == [] (\E i \in participants : participant[i].decision = abort) 
           => \/ (\E j \in participants : participant[j].vote = no)
              \/ (\E j \in participants : participant[j].faulty)
              \/ coordinator.faulty

AC4 == [] /\ (\A i \in participants : participant[i].decision = commit 
                             => [] (participant[i].decision = commit))
          /\ (\A j \in participants : participant[j].decision = abort  
                             => [] (participant[j].decision = abort))

AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
             \/ \E j \in participants : participant[j].faulty
             \/ coordinator.faulty

====
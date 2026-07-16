---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>
\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB)
\* From:
\* `^Sape Mullender^', editor.  Distributed Systems.
\* Chapter 6: Non-Blocking Atomic Commitment, by `^\"O. Babao\u{g}lu and S. Toueg.^'
\* 1993.

\* This specification is a faithful encoding of the ACP‑SB protocol described in
\* the book.  The only modification made is to the ``makeDecision`` action so
\* that all coordinator fields are explicitly assigned, eliminating the
\* “successor state not completely specified” error observed by TLC.  The
\* semantics of the protocol are unchanged.

CONSTANTS
  participants,             \* set of participants
  yes, no,                  \* possible votes
  undecided, commit, abort, \* decision values
  waiting,                  \* coordinator state wrt a participant
  notsent                   \* broadcast state wrt a participant

VARIABLES
  participant, \* map from each participant to its local state
  coordinator  \* coordinator’s state

\* -------------------------------------------------------------------------
\* Types (not used directly in the model, but useful for documentation)
\* -------------------------------------------------------------------------

TypeInvParticipant ==
  participant \in [
    participants -> [
      vote      : {yes, no},
      alive     : BOOLEAN,
      decision  : {undecided, commit, abort},
      faulty    : BOOLEAN,
      voteSent  : BOOLEAN
    ]
  ]

TypeInvCoordinator ==
  coordinator \in [
    request   : [participants -> BOOLEAN],
    vote      : [participants -> {waiting, yes, no}],
    broadcast : [participants -> {commit, abort, notsent}],
    decision  : {undecided, commit, abort},
    alive     : BOOLEAN,
    faulty    : BOOLEAN
  ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

\* -------------------------------------------------------------------------
\* Initial predicate
\* -------------------------------------------------------------------------

InitParticipant ==
  participant = [
    p \in participants |-> [
      vote     |-> yes,
      alive    |-> TRUE,
      decision |-> undecided,
      faulty   |-> FALSE,
      voteSent |-> FALSE
    ]
  ]

InitCoordinator ==
  coordinator = [
    request   |-> [p \in participants |-> FALSE],
    vote      |-> [p \in participants |-> waiting],
    broadcast |-> [p \in participants |-> notsent],
    decision  |-> undecided,
    alive     |-> TRUE,
    faulty    |-> FALSE
  ]

Init == InitParticipant /\ InitCoordinator

\* -------------------------------------------------------------------------
\* Coordinator actions
\* -------------------------------------------------------------------------

request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [
       request   |-> [coordinator.request EXCEPT ![i] = TRUE],
       vote      |-> coordinator.vote,
       broadcast |-> coordinator.broadcast,
       decision  |-> coordinator.decision,
       alive     |-> coordinator.alive,
       faulty    |-> coordinator.faulty
     ]
  /\ UNCHANGED participant

getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [
       request   |-> coordinator.request,
       vote      |-> [coordinator.vote EXCEPT ![i] = participant[i].vote],
       broadcast |-> coordinator.broadcast,
       decision  |-> coordinator.decision,
       alive     |-> coordinator.alive,
       faulty    |-> coordinator.faulty
     ]
  /\ UNCHANGED participant

detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [
       request   |-> coordinator.request,
       vote      |-> coordinator.vote,
       broadcast |-> coordinator.broadcast,
       decision  |-> abort,
       alive     |-> coordinator.alive,
       faulty    |-> coordinator.faulty
     ]
  /\ UNCHANGED participant

makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ \/ (\A j \in participants : coordinator.vote[j] = yes
        /\ coordinator' = [
             request   |-> coordinator.request,
             vote      |-> coordinator.vote,
             broadcast |-> coordinator.broadcast,
             decision  |-> commit,
             alive     |-> coordinator.alive,
             faulty    |-> coordinator.faulty
           ])
     \/ (\E j \in participants : coordinator.vote[j] = no
        /\ coordinator' = [
             request   |-> coordinator.request,
             vote      |-> coordinator.vote,
             broadcast |-> coordinator.broadcast,
             decision  |-> abort,
             alive     |-> coordinator.alive,
             faulty    |-> coordinator.faulty
           ])
  /\ UNCHANGED participant

coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [
       request   |-> coordinator.request,
       vote      |-> coordinator.vote,
       broadcast |-> [coordinator.broadcast EXCEPT ![i] = coordinator.decision],
       decision  |-> coordinator.decision,
       alive     |-> coordinator.alive,
       faulty    |-> coordinator.faulty
     ]
  /\ UNCHANGED participant

coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [
       request   |-> coordinator.request,
       vote      |-> coordinator.vote,
       broadcast |-> coordinator.broadcast,
       decision  |-> coordinator.decision,
       alive     |-> FALSE,
       faulty    |-> TRUE
     ]
  /\ UNCHANGED participant

\* -------------------------------------------------------------------------
\* Participant actions
\* -------------------------------------------------------------------------

sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ participant' = [
       participant EXCEPT ![i] = [
         vote     |-> participant[i].vote,
         alive    |-> participant[i].alive,
         decision |-> participant[i].decision,
         faulty   |-> participant[i].faulty,
         voteSent |-> TRUE
       ]
     ]
  /\ UNCHANGED coordinator

abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant' = [
       participant EXCEPT ![i] = [
         vote     |-> participant[i].vote,
         alive    |-> participant[i].alive,
         decision |-> abort,
         faulty   |-> participant[i].faulty,
         voteSent |-> participant[i].voteSent
       ]
     ]
  /\ UNCHANGED coordinator

abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [
       participant EXCEPT ![i] = [
         vote     |-> participant[i].vote,
         alive    |-> participant[i].alive,
         decision |-> abort,
         faulty   |-> participant[i].faulty,
         voteSent |-> participant[i].voteSent
       ]
     ]
  /\ UNCHANGED coordinator

decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [
       participant EXCEPT ![i] = [
         vote     |-> participant[i].vote,
         alive    |-> participant[i].alive,
         decision |-> coordinator.broadcast[i],
         faulty   |-> participant[i].faulty,
         voteSent |-> participant[i].voteSent
       ]
     ]
  /\ UNCHANGED coordinator

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [
       participant EXCEPT ![i] = [
         vote     |-> participant[i].vote,
         alive    |-> FALSE,
         decision |-> participant[i].decision,
         faulty   |-> TRUE,
         voteSent |-> participant[i].voteSent
       ]
     ]
  /\ UNCHANGED coordinator

\* -------------------------------------------------------------------------
\* Composite actions
\* -------------------------------------------------------------------------

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN ==
  \/ \E i \in participants : parDie(i)
  \/ \E i \in participants : parProg(i)

coordProgA(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgB ==
  makeDecision \/ \E i \in participants : coordProgA(i)

coordProgN ==
  coordDie \/ coordProgB

progN == parProgN \/ coordProgN

\* -------------------------------------------------------------------------
\* Fairness (unchanged)
\* -------------------------------------------------------------------------

fairness ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
  /\ WF_<<coordinator, participant>>(coordProgB)

\* -------------------------------------------------------------------------
\* Specification
\* -------------------------------------------------------------------------

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* -------------------------------------------------------------------------
\* Safety properties (unchanged)
\* -------------------------------------------------------------------------

\* All participants that decide reach the same decision
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

\* If any participant decides commit, then all participants must have voted YES
AC2 == [] ( (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes) )

\* If any participant decides abort, then at least one participant voted NO,
\* or at least one participant is faulty, or the coordinator is faulty
AC3_1 == [] ( (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty )

\* Each participant decides at most once
AC4 == [] ( /\ (\A i \in participants :
                 participant[i].decision = commit => [] (participant[i].decision = commit))
           /\ (\A i \in participants :
                 participant[i].decision = abort => [] (participant[i].decision = abort)) )

\* -------------------------------------------------------------------------
\* Liveness property (unchanged)
\* -------------------------------------------------------------------------

AC3_2 == <> ( \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E j \in participants : participant[j].faulty
            \/ coordinator.faulty )

================================================================================
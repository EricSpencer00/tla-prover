---- MODULE ACP_SB ----
\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB), from Babaoglu and Toueg's work on
\* non-blocking atomic commitment. A coordinator collects votes from participants and
\* broadcasts a commit/abort decision; if the coordinator crashes mid-broadcast, participants
\* can be left undecided, which is why this variant blocks rather than being truly
\* non-blocking. Both the coordinator and participants may crash silently.
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, pdecision, pvote, pdecided, pfaulty, prequested, pmsg, pfinal, alive, faulty

vars == <<pstate, pdecision, pvote, pdecided, pfaulty, prequested, pmsg, pfinal, alive, faulty>>

ReceivedAll == \A p \in participants : pstate[p] = yes \/ pstate[p] = no
VotedAll == \A p \in participants : pvote[p] # waiting

TypeInv ==
  /\ pstate \in [participants -> {yes, no}]
  /\ pdecision \in [participants -> {undecided, commit, abort}]
  /\ pvote \in [participants -> {yes, no, waiting}]
  /\ pdecided \in [participants -> BOOLEAN]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ prequested \in [participants -> BOOLEAN]
  /\ pmsg \in [participants -> {notsent, commit, abort}]
  /\ pfinal \in {undecided, commit, abort}
  /\ alive \in {TRUE, FALSE}
  /\ faulty \in BOOLEAN

Init ==
  /\ pstate \in [participants -> {yes, no}]
  /\ pdecision = [p \in participants |-> undecided]
  /\ pvote = [p \in participants |-> waiting]
  /\ pdecided = [p \in participants |-> FALSE]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ prequested = [p \in participants |-> FALSE]
  /\ pmsg = [p \in participants |-> notsent]
  /\ pfinal = undecided
  /\ alive = TRUE
  /\ faulty = FALSE

\* Coordinator actions (only while alive and not yet faulty):
\* SendVoteReq: emit a vote request to a participant. ReceiveVote: absorb a vote already
\* sent by a participant. AbortDetect: on noticing a participant died without voting, abort.
\* MakeDecision: commit iff all votes are yes, otherwise abort. Broadcast: send out the
\* final decision (one participant at a time, simple broadcast). Die: crash silently.
SendVoteReq(p) ==
  /\ alive
  /\ ~prequested[p]
  /\ prequested' = [prequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, pdecision, pvote, pdecided, pfaulty, pmsg, pfinal, alive, faulty>>

ReceiveVote(p) ==
  /\ alive
  /\ pfinal = undecided
  /\ prequested[p]
  /\ pvote[p] = waiting
  /\ pstate[p] # yes
  /\ pvote[p] # no
  /\ pvote' = [pvote EXCEPT ![p] = pstate[p]]
  /\ UNCHANGED <<pstate, pdecision, pdecided, pfaulty, prequested, pmsg, pfinal, alive, faulty>>

DetectFault(p) ==
  /\ alive
  /\ pfinal = undecided
  /\ prequested[p]
  /\ pvote[p] = waiting
  /\ pfaulty[p]
  /\ pfinal' = abort
  /\ UNCHANGED <<pstate, pdecision, pvote, pdecided, pfaulty, prequested, pmsg, alive, faulty>>

MakeDecision ==
  /\ alive
  /\ pfinal = undecided
  /\ prequested = [p \in participants |-> TRUE]
  /\ VotedAll
  /\ pfinal' = IF \A p \in participants : pvote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pstate, pdecision, pvote, pdecided, pfaulty, prequested, pmsg, alive, faulty>>

Broadcast(p) ==
  /\ alive
  /\ pfinal # undecided
  /\ pmsg[p] = notsent
  /\ pmsg' = [pmsg EXCEPT ![p] = pfinal]
  /\ UNCHANGED <<pstate, pdecision, pvote, pdecided, pfaulty, prequested, pfinal, alive, faulty>>

Die ==
  /\ alive
  /\ alive' = FALSE
  /\ faulty' = TRUE
  /\ UNCHANGED <<pstate, pdecision, pvote, pdecided, pfaulty, prequested, pmsg, pfinal>>

\* Participant actions (only while alive and not yet faulty):
\* SendVote: emit a vote after receiving a request. AbortOnVote: unilaterally abort on a no
\* vote. AbortOnReqTimeout: abort if the coordinator died without requesting. Decide: adopt
\* the decision broadcast by the coordinator. Die: crash silently.
SendParticipantVote(p) ==
  /\ pstate[p] # yes
  /\ pstate[p] # no
  /\ pvote[p] = waiting
  /\ prequested[p]
  /\ alive
  /\ pvote' = [pvote EXCEPT ![p] = pstate[p]]
  /\ UNCHANGED <<pstate, pdecision, pdecided, pfaulty, prequested, pmsg, pfinal, alive, faulty>>

AbortOnVote(p) ==
  /\ alive
  /\ ~pdecided[p]
  /\ pvote[p] = no
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ pdecided' = [pdecided EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, pvote, pfaulty, prequested, pmsg, pfinal, alive, faulty>>

AbortOnReqTimeout(p) ==
  /\ alive
  /\ ~pdecided[p]
  /\ ~alive
  /\ pfinal = undecided
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ pdecided' = [pdecided EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, pvote, pfaulty, prequested, pmsg, pfinal, alive, faulty>>

Decide(p) ==
  /\ alive
  /\ ~pdecided[p]
  /\ pmsg[p] # notsent
  /\ pdecision' = [pdecision EXCEPT ![p] = pmsg[p]]
  /\ pdecided' = [pdecided EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, pvote, pfaulty, prequested, pmsg, pfinal, alive, faulty>>

DieParticipant(p) ==
  /\ ~alive
  /\ ~pfaulty[p]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, pdecision, pvote, pdecided, prequested, pmsg, pfinal, alive, faulty>>

Next ==
  \/ \E p \in participants : SendVoteReq(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ Broadcast(p) \/ DieParticipant(p) \/ SendParticipantVote(p) \/ AbortOnVote(p) \/ AbortOnReqTimeout(p) \/ Decide(p)
  \/ MakeDecision
  \/ Die

Spec == Init /\ [][Next]_vars /\ WF_vars(SendVoteReq(CHOICE participants)) /\ WF_vars(ReceiveVote(CHOICE participants)) /\ WF_vars(MakeDecision) /\ WF_vars(Broadcast(CHOICE participants))

\* No two participants ever disagree on the outcome: one cannot commit while another aborts.
Agreement ==
  \A p, q \in participants : ~(pdecision[p] = commit /\ pdecision[q] = abort)

\* Commit validity: if anyone commits, every participant must have voted yes.
CommitValidity ==
  \A p \in participants : (pdecision[p] = commit) => (\A q \in participants : pstate[q] = yes)

\* Abort validity: if anyone aborts, some participant voted no or some participant crashed or the coordinator crashed.
AbortValidity ==
  \A p \in participants : (pdecision[p] = abort) => (\E q \in participants : pstate[q] = no \/ pfaulty[q] \/ faulty)

\* Irrevocability: once a participant commits it stays committed, once it aborts it stays aborted.
Irrevocable ==
  \A p \in participants : (pdecision[p] = commit => (pdecision' [p] = commit \/ pdecision' [p] = undecided)) /\ (pdecision[p] = abort => (pdecision' [p] = abort \/ pdecision' [p] = undecided))

\* Liveness: either every participant decides, or at least one participant crashes, or the coordinator crashes.
DecisionOrFailure ==
  <>(\A p \in participants : pdecided[p]) \/ <>(\E p \in participants : pfaulty[p]) \/ <>(faulty)

====
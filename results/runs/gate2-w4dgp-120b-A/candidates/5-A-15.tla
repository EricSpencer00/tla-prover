---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* The Atomic Commitment Protocol with Simple Broadcast (ACP-SB) from Babaoglu
\* and Toueg.  A coordinator collects votes from participants and then decides
\* commit/abort, broadcasting its decision.  Broadcast is simple and sequential,
\* so a coordinator failure during broadcast can leave some participants undecided
\* -- this is a blocking protocol, captured by property AC3 below (termination
\* for every non-faulty participant is NOT guaranteed).

VARIABLES vote, pAlive, decision, faulty, sent, rq, rcv, bc, cDecision, cAlive

vars == <<vote, pAlive, decision, faulty, sent, rq, rcv, bc, cDecision, cAlive>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ rq \in [participants -> {notsent, waiting}]
  /\ rcv \in [participants -> {yes, no, waiting}]
  /\ bc \in [participants -> {notsent, commit, abort}]
  /\ cDecision \in {undecided, commit, abort}
  /\ cAlive \in BOOLEAN

Init ==
  /\ \E v \in {yes, no} :
       /\ vote = [p \in participants |-> v]
       /\ cDecision = undecided
  /\ pAlive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ rq = [p \in participants |-> notsent]
  /\ rcv = [p \in participants |-> waiting]
  /\ bc = [p \in participants |-> notsent]
  /\ cAlive = TRUE

\* Coordinator sends a vote request to a participant.
SendReq(p) ==
  /\ cAlive
  /\ rq[p] = notsent
  /\ rq' = [rq EXCEPT ![p] = waiting]
  /\ UNCHANGED <<vote, pAlive, decision, faulty, sent, rcv, bc, cDecision>>

\* Coordinator receives a participant's vote (only once that participant has sent it).
RcvVote(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ rq[p] # notsent
  /\ rcv[p] = waiting
  /\ sent[p]
  /\ rcv' = [rcv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, pAlive, decision, faulty, sent, rq, bc, cDecision, cAlive>>

\* Failure detection: coordinator notices a participant died before voting and aborts.
DetectFailure(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ rq[p] # notsent
  /\ rcv[p] = waiting
  /\ ~pAlive[p]
  /\ cDecision' = abort
  /\ UNCHANGED <<vote, pAlive, decision, faulty, sent, rq, rcv, bc, cAlive>>

\* Coordinator decides commit only if all votes are yes; otherwise abort.
Decide ==
  /\ cAlive
  /\ cDecision = undecided
  /\ \A p \in participants : rq[p] # notsent => rcv[p] # waiting
  /\ cDecision' = IF \A p \in participants : rcv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, pAlive, decision, faulty, sent, rq, rcv, bc, cAlive>>

\* Simple broadcast: the coordinator sends its decision to one participant at a time.
Broadcast(p) ==
  /\ cAlive
  /\ cDecision # undecided
  /\ bc[p] = notsent
  /\ bc' = [bc EXCEPT ![p] = cDecision]
  /\ UNCHANGED <<vote, pAlive, decision, faulty, sent, rq, rcv, cDecision, cAlive>>

DieCoordinator ==
  /\ cAlive
  /\ cAlive' = FALSE
  /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
  /\ UNCHANGED <<vote, pAlive, decision, sent, rq, rcv, bc, cDecision>>

\* Participant sends its vote to the coordinator.
SendVote(p) ==
  /\ pAlive[p]
  /\ rq[p] # notsent
  /\ ~sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, pAlive, decision, faulty, rq, rcv, bc, cDecision, cAlive>>

\* A participant with a no vote aborts immediately.
AbortVote(p) ==
  /\ pAlive[p]
  /\ decision[p] = undecided
  /\ sent[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, pAlive, sent, rq, rcv, bc, cDecision, cAlive, faulty>>

\* A participant times out waiting for a vote request (the coordinator died); aborts.
AbortTimeout(p) ==
  /\ pAlive[p]
  /\ decision[p] = undecided
  /\ ~cAlive
  /\ rq[p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, pAlive, sent, rq, rcv, bc, cDecision, cAlive, faulty>>

\* A participant adopts the coordinator's decision once it receives it.
DecideOnBroadcast(p) ==
  /\ pAlive[p]
  /\ decision[p] = undecided
  /\ bc[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = bc[p]]
  /\ UNCHANGED <<vote, pAlive, sent, rq, rcv, bc, cDecision, cAlive, faulty>>

Die(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sent, rq, rcv, bc, cDecision, cAlive>>

ParticipantActions ==
  \E p \in participants :
    \/ SendVote(p)
    \/ AbortVote(p)
    \/ AbortTimeout(p)
    \/ DecideOnBroadcast(p)
    \/ Die(p)

CoordinatorActions ==
  \/ Decide
  \/ DieCoordinator
  \E p \in participants :
    \/ SendReq(p)
    \/ RcvVote(p)
    \/ DetectFailure(p)
    \/ Broadcast(p)

Next ==
  \/ ParticipantActions
  \/ CoordinatorActions

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ParticipantActions)
  /\ WF_vars(CoordinatorActions)

\* SAFETY: no two participants ever decide differently.
AC1 ==
  \A p, q \in participants :
    ~(decision[p] = commit /\ decision[q] = abort)

\* Commit only if all participants voted yes.
AC2 ==
  \A p \in participants :
    decision[p] = commit => (\A q \in participants : vote[q] = yes)

\* Abort only if a no vote or a fault was observed.
AC3 ==
  \A p \in participants :
    decision[p] = abort =>
      \/ \E q \in participants : vote[q] = no
      \/ \E q \in participants : faulty[q]
      \/ ~cAlive

\* Irreversibility: once a participant decides it never flips.
AC4 ==
  \A p \in participants :
    (decision[p] = commit => decision[p] = commit)
      /\ (decision[p] = abort => decision[p] = abort)

\* LIVENESS: either every participant decides, or a fault is observed (the
\* coordinator can crash silently during broadcast, so termination is not
\* guaranteed for every non-faulty participant -- this is the blocking case).
AC3Progress ==
  <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ ~cAlive)

====
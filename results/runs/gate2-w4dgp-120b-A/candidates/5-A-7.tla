---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordDecision, coordAlive, coordFaulty, coordSent, coordRecv, coordBroadcast,
          voted, alive, decision, faulty, voteSent

vars == <<coordDecision, coordAlive, coordFaulty, coordSent, coordRecv, coordBroadcast,
          voted, alive, decision, faulty, voteSent>>

Participants == participants

TypeInv ==
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordSent \in [Participants -> BOOLEAN]
  /\ coordRecv \in [Participants -> {yes, no, waiting}]
  /\ coordBroadcast \in [Participants -> {commit, abort, notsent}]
  /\ voted \in [Participants -> {yes, no}]
  /\ alive \in [Participants -> BOOLEAN]
  /\ decision \in [Participants -> {commit, abort, undecided}]
  /\ faulty \in [Participants -> BOOLEAN]
  /\ voteSent \in [Participants -> BOOLEAN]

\* The coordinator requests each participant's vote.
RequestVote(p) ==
  /\ coordAlive
  /\ ~coordSent[p]
  /\ coordSent' = [coordSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordDecision, coordAlive, coordFaulty, coordRecv, coordBroadcast,
                voted, alive, decision, voteSent>>

\* The coordinator receives a participant's vote.
ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordSent[p]
  /\ coordRecv[p] = waiting
  /\ voteSent[p]
  /\ coordRecv' = [coordRecv EXCEPT ![p] = voted[p]]
  /\ UNCHANGED <<coordDecision, coordAlive, coordFaulty, coordSent, coordBroadcast,
                voted, alive, decision, voteSent>>

\* The coordinator detects a participant fault and decides abort.
DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordSent[p]
  /\ coordRecv[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<coordAlive, coordFaulty, coordSent, coordRecv, coordBroadcast,
                voted, alive, decision, voteSent>>

\* The coordinator makes a decision once all votes are in.
MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in Participants : coordRecv[p] # waiting
  /\ coordDecision' = IF \A p \in Participants : coordRecv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<coordAlive, coordFaulty, coordSent, coordRecv, coordBroadcast,
                voted, alive, decision, voteSent>>

\* Simple broadcast: the coordinator sends its decision to one participant at a time.
Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordBroadcast[p] = notsent
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<coordDecision, coordAlive, coordFaulty, coordSent, coordRecv,
                voted, alive, decision, voteSent>>

DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordDecision, coordSent, coordRecv, coordBroadcast,
                voted, alive, decision, voteSent>>

\* A live participant sends its vote once it has received a request.
SendVote(p) ==
  /\ alive[p]
  /\ coordSent[p]
  /\ ~voteSent[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordDecision, coordAlive, coordFaulty, coordSent, coordRecv,
                voted, alive, decision, coordBroadcast>>

\* A no-voter aborts unilaterally.
AbortOnNo(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ voteSent[p]
  /\ voted[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordDecision, coordAlive, coordFaulty, coordSent, coordRecv,
                voted, alive, faulty, voteSent, coordBroadcast>>

\* A participant times out waiting for the coordinator's request and aborts.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ coordSent[p] = FALSE
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordDecision, coordAlive, coordFaulty, coordSent, coordRecv,
                voted, alive, faulty, voteSent, coordBroadcast>>

\* The participant adopts the coordinator's broadcasted decision.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordAlive
  /\ coordBroadcast[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = coordBroadcast[p]]
  /\ UNCHANGED <<coordDecision, coordAlive, coordFaulty, coordSent, coordRecv,
                voted, alive, faulty, voteSent, coordBroadcast>>

DieParticipant(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordDecision, coordAlive, coordFaulty, coordSent, coordRecv,
                voted, decision, voteSent, coordBroadcast>>

DecideAny == \E p \in Participants : Decide(p)

Next ==
  \/ \E p \in Participants : RequestVote(p)
  \/ \E p \in Participants : ReceiveVote(p)
  \/ \E p \in Participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in Participants : Broadcast(p)
  \/ DieCoordinator
  \/ \E p \in Participants : SendVote(p)
  \/ \E p \in Participants : AbortOnNo(p)
  \/ \E p \in Participants : AbortOnTimeout(p)
  \/ DecideAny
  \/ \E p \in Participants : DieParticipant(p)

\* SAFETY: no two participants ever decide differently -- commit vs abort is
\* mutually exclusive, so AC5 (termination for all non-faulty participants) does
\* not hold in this simple broadcast version, but agreement and validity must.
Agreement ==
  ~(\E p \in Participants : decision[p] = commit /\ \E q \in Participants : decision[q] = abort)

CommitValidity ==
  (\E p \in Participants : decision[p] = commit) => (\A p \in Participants : voted[p] = yes)

AbortValidity ==
  (\E p \in Participants : decision[p] = abort) =>
    (\E p \in Participants : voted[p] = no \/ faulty[p] \/ coordFaulty)

Irreversibility ==
  \A p \in Participants :
    /\ (decision[p] = commit => decision[p] = commit)
    /\ (decision[p] = abort => decision[p] = abort)

\* LIVENESS: either everyone decides, or some participant/crash is observed.
EventualDecision ==
  <>(\A p \in Participants : decision[p] # undecided \/ faulty[p] \/ coordFaulty)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_vars(\E p \in Participants : RequestVote(p) \/ SendVote(p))
  /\ SF_vars(\E p \in Participants : ReceiveVote(p))
  /\ SF_vars(\E p \in Participants : DetectFault(p) \/ AbortOnNo(p) \/ AbortOnTimeout(p))
  /\ SF_vars(MakeDecision)
  /\ SF_vars(DecideAny)

====
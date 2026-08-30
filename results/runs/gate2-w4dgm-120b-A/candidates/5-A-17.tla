---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participantVote, participantAlive, participantDecision, participantFaulty,
          participantSent, coordReqSent, coordVoteRecv, coordDecisionSent,
          coordDecision, coordAlive, coordFaulty

vars == << participantVote, participantAlive, participantDecision,
            participantFaulty, participantSent, coordReqSent, coordVoteRecv,
            coordDecisionSent, coordDecision, coordAlive, coordFaulty >>

TypeOK ==
  /\ participantVote \in [participants -> {yes, no}]
  /\ participantAlive \in [participants -> BOOLEAN]
  /\ participantDecision \in [participants -> {undecided, commit, abort}]
  /\ participantFaulty \in [participants -> BOOLEAN]
  /\ participantSent \in [participants -> BOOLEAN]
  /\ coordReqSent \in [participants -> BOOLEAN]
  /\ coordVoteRecv \in [participants -> {waiting, yes, no}]
  /\ coordDecisionSent \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

\* A coordinator crash during broadcast can strand a participant undecided,
\* so this liveness property does not hold under all runs (only the
\* non-blocking variant AC5 does); it is the other AC liveness properties
\* that are expected to hold, and the specification never lumps an
\* immediate-decision abort under "coord died during broadcast" as a
\* liveness shortcut -- the abort path is an actual action below.
EventuallyDecide == <>(\E p \in participants : participantDecision[p] # undecided)

Init ==
  /\ participantVote \in [participants -> {yes, no}]
  /\ participantAlive = [p \in participants |-> TRUE]
  /\ participantDecision = [p \in participants |-> undecided]
  /\ participantFaulty = [p \in participants |-> FALSE]
  /\ participantSent = [p \in participants |-> FALSE]
  /\ coordReqSent = [p \in participants |-> FALSE]
  /\ coordVoteRecv = [p \in participants |-> waiting]
  /\ coordDecisionSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator actions.
SendRequest(p) ==
  /\ coordAlive
  /\ ~coordReqSent[p]
  /\ coordReqSent' = [coordReqSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSent, coordVoteRecv,
                 coordDecisionSent, coordDecision, coordAlive, coordFaulty >>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants : coordReqSent[q]
  /\ coordVoteRecv[p] = waiting
  /\ participantSent[p]
  /\ coordVoteRecv' = [coordVoteRecv EXCEPT ![p] = participantVote[p]]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSent, coordReqSent,
                 coordDecisionSent, coordDecision, coordAlive, coordFaulty >>

DetectParticipantFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants : coordReqSent[q]
  /\ coordVoteRecv[p] = waiting
  /\ ~participantAlive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSent, coordReqSent,
                 coordVoteRecv, coordDecisionSent, coordAlive, coordFaulty >>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordVoteRecv[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordVoteRecv[p] = yes
                       THEN commit ELSE abort
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSent, coordReqSent,
                 coordVoteRecv, coordDecisionSent, coordAlive, coordFaulty >>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordDecisionSent[p] = notsent
  /\ coordDecisionSent' = [coordDecisionSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSent, coordReqSent,
                 coordVoteRecv, coordDecision, coordAlive, coordFaulty >>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSent, coordReqSent,
                 coordVoteRecv, coordDecisionSent, coordDecision >>

\* Participant actions.
SendVote(p) ==
  /\ participantAlive[p]
  /\ coordReqSent[p]
  /\ ~participantSent[p]
  /\ participantSent' = [participantSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, coordReqSent, coordVoteRecv,
                 coordDecisionSent, coordDecision, coordAlive, coordFaulty >>

UnanimousAbort(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ participantSent[p]
  /\ participantVote[p] = no
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                 participantSent, coordReqSent, coordVoteRecv,
                 coordDecisionSent, coordDecision, coordAlive, coordFaulty >>

AbortOnTimeout(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ ~coordAlive
  /\ ~coordReqSent[p]
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                 participantSent, coordReqSent, coordVoteRecv,
                 coordDecisionSent, coordDecision, coordAlive, coordFaulty >>

DecideOnCoordinatorBroadcast(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ coordDecisionSent[p] # notsent
  /\ participantDecision' = [participantDecision EXCEPT ![p] = coordDecisionSent[p]]
  /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                 participantSent, coordReqSent, coordVoteRecv,
                 coordDecisionSent, coordDecision, coordAlive, coordFaulty >>

ParticipantDie(p) ==
  /\ participantAlive[p]
  /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
  /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << participantVote, participantDecision, participantSent,
                 coordReqSent, coordVoteRecv, coordDecisionSent, coordDecision,
                 coordAlive, coordFaulty >>

\* Participant progress (non-death) actions get weak fairness; death actions
\* are excluded from fairness so a crash can always remain available.
Next ==
  \/ \E p \in participants :
       \/ SendRequest(p) \/ ReceiveVote(p) \/ DetectParticipantFault(p)
       \/ BroadcastDecision(p) \/ SendVote(p) \/ UnanimousAbort(p)
       \/ AbortOnTimeout(p) \/ DecideOnCoordinatorBroadcast(p)
       \/ ParticipantDie(p)
  \/ MakeDecision
  \/ CoordDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendRequest(p))
  /\ WF_vars(\E p \in participants : ReceiveVote(p))
  /\ WF_vars(\E p \in participants : BroadcastDecision(p))
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : UnanimousAbort(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
  /\ WF_vars(\E p \in participants : DecideOnCoordinatorBroadcast(p))

\* No two participants decide differently.
Agreement ==
  \A p, q \in participants :
    (participantDecision[p] = commit /\ participantDecision[q] = abort) => FALSE

\* A commit requires every participant's vote to have been yes.
CommitValidity ==
  (\E p \in participants : participantDecision[p] = commit)
    => (\A p \in participants : participantVote[p] = yes)

\* An abort is justified by a no vote, a participant fault, or a coordinator fault.
AbortValidity ==
  (\E p \in participants : participantDecision[p] = abort)
    => (\E p \in participants : participantVote[p] = no \/ participantFaulty[p])
         \/ coordFaulty

\* A decision, once made by a participant, never flips.
Irrevocability ==
  \A p \in participants :
    (participantDecision[p] = commit => participantDecision' = [participantDecision EXCEPT ![p] = commit])
    /\ (participantDecision[p] = abort => participantDecision' = [participantDecision EXCEPT ![p] = abort])

TypeInv == TypeOK

====
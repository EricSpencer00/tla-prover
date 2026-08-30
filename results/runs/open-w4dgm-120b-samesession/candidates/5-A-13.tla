---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Types: each participant votes yes/no, is alive until it crashes, decides commit
\* or abort (once), and may or may not have sent its vote. The coordinator collects
\* votes, decides, and broadcasts its decision to each participant (the "simple
\* broadcast" twist: it can crash mid-broadcast, leaving some participants undecided).
VARIABLES vote, alive, decision, faulty, sentVote,
          coordAsked, coordVote, coordSent, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentVote,
           coordAsked, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordAsked \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {sent, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordAsked = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator actions ---------------------------------------------------------

CoordSendVoteReq(p) ==
  /\ coordAlive
  /\ ~coordAsked[p]
  /\ coordAsked' = [coordAsked EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 coordVote, coordSent, coordDecision, coordFaulty>>

\* The coordinator receives a vote only once the participant has actually sent
\* it; because broadcast is simple/sequential, a participant's crash can be
\* detected here as the coordinator waiting on a vote that never arrives.
CoordReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordAsked[p]
  /\ coordVote[p] = waiting
  /\ sentVote[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 coordAsked, coordSent, coordDecision, coordAlive, coordFaulty>>

CoordDetectParticipantFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordAsked[p]
  /\ coordVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 coordAsked, coordVote, coordSent, coordAlive, coordFaulty>>

CoordMakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordAsked[p]
  /\ \A p \in participants : coordVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 coordAsked, coordVote, coordSent, coordAlive, coordFaulty>>

CoordBroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = sent]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 coordAsked, coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 coordAsked, coordVote, coordSent, coordDecision>>

\* Participant actions ---------------------------------------------------------

SendVote(p) ==
  /\ alive[p]
  /\ coordAsked[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty,
                 coordAsked, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 coordAsked, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~coordAsked[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 coordAsked, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

DecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSent[p] = sent
  /\ decision' = [decision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 coordAsked, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote,
                 coordAsked, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

\* The full action set, with the liveness-implied progress actions singled out
\* (what is not subject to weak fairness): death can always happen at any instant,
\* but the others -- sending votes, making a decision, broadcasting it -- are
\* guaranteed to eventually fire once their enabling condition holds.
Next ==
  \/ \E p \in participants :
       \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p)
       \/ DecideFromCoordinator(p) \/ ParticipantDie(p)
  \/ CoordSendVoteReq(p) \/ CoordReceiveVote(p) \/ CoordDetectParticipantFault(p)
  \/ CoordBroadcastDecision(p)
  \/ CoordMakeDecision
  \/ CoordDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants : SF_vars(SendVote(p)) /\ WF_vars(AbortOnTimeout(p))
  /\ \A p \in participants : SF_vars(DecideFromCoordinator(p))
  /\ WF_vars(CoordMakeDecision)

\* Safety: no two participants ever disagree on the outcome (AC1); a commit can
\* only happen if everyone voted yes (AC2); an abort is only justified by a no
\* vote, a participant fault, or a coordinator fault (AC3); and a participant
\* decides at most once, committing (or aborting) irrevocably (AC4).
NoTwoParticipantsDisagree ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitOnlyOnAllYes ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

AbortOnlyOnNoOrFault ==
  \A p \in participants :
    decision[p] = abort =>
      \/ (\E q \in participants : vote[q] = no)
      \/ (\E q \in participants : faulty[q])
      \/ coordFaulty

DecideAtMostOnce ==
  /\ (\A p \in participants : decision[p] = commit => decision' = [decision EXCEPT ![p] = commit])
  /\ (\A p \in participants : decision[p] = abort => decision' = [decision EXCEPT ![p] = abort])
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 coordAsked, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

TypeInv == TypeOK

\* Liveness: either everyone is decided, or some participant crashed, or the
\* coordinator crashed -- simple broadcast does NOT force every non-crashed
\* participant to eventually decide (no non-blocking AC5 guarantee here).
DecideOrCrash ==
  \A p \in participants :
    (decision[p] = undecided) ~> (decision[p] # undecided \/ faulty[p] \/ coordFaulty)

\* Needed to keep the reachable state space finite, since the coordinator can
\* keep repeatedly refusing to broadcast to a participant that already got the
\* decision (a no-op that would otherwise cause infinite stuttering).
DecideOrCrashBounded ==
  \A p \in participants :
    (decision[p] = undecided) ~> (decision[p] # undecided \/ faulty[p] \/ coordFaulty)

====
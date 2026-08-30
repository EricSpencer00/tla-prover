---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Reliable broadcast: a participant pre-declares the received decision
\* (its own forwarding-table entry) and forwards it to every other participant
\* before finalizing. This is what keeps the protocol non-blocking if the
\* coordinator crashes mid-broadcast.
VARIABLES decision, pstate, alive, faulty, sentVote, coordState, forward

vars == <<decision, pstate, alive, faulty, sentVote, coordState, forward>>

TypeOK ==
  /\ decision \in [participants -> {yes, no, undecided}]
  /\ pstate \in [participants -> {commit, abort, waiting}]
  /\ alive \in [participants -> BOOLEAN]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordState \in [req : BOOLEAN, vote : {yes, no, undecided}, bcast : participants \cup {notsent}, decision : {commit, abort, undecided}, alive : BOOLEAN, faulty : BOOLEAN]
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ decision = [p \in participants |-> undecided]
  /\ pstate = [p \in participants |-> waiting]
  /\ alive = [p \in participants |-> TRUE]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordState = [req |-> FALSE, vote |-> undecided, bcast |-> notsent, decision |-> undecided, alive |-> TRUE, faulty |-> FALSE]
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

CoordSendReq ==
  /\ coordState.alive
  /\ ~coordState.req
  /\ coordState' = [coordState EXCEPT !.req = TRUE]
  /\ UNCHANGED <<decision, pstate, alive, faulty, sentVote, forward>>

CoordGetVote(p) ==
  /\ coordState.alive
  /\ coordState.req
  /\ decision[p] # undecided
  /\ coordState.vote = undecided
  /\ coordState' = [coordState EXCEPT !.vote = decision[p]]
  /\ UNCHANGED <<decision, pstate, alive, faulty, sentVote, forward>>

CoordDetectFault(p) ==
  /\ coordState.alive
  /\ decision[p] = no
  /\ coordState.vote = undecided
  /\ coordState' = [coordState EXCEPT !.vote = no]
  /\ UNCHANGED <<decision, pstate, alive, faulty, sentVote, forward>>

CoordDecide ==
  /\ coordState.alive
  /\ coordState.req
  /\ coordState.vote = yes
  /\ coordState.decision = undecided
  /\ coordState' = [coordState EXCEPT !.decision = commit]
  /\ UNCHANGED <<decision, pstate, alive, faulty, sentVote, forward>>

CoordBroadcast(p) ==
  /\ coordState.alive
  /\ coordState.decision # undecided
  /\ coordState.bcast = notsent
  /\ coordState' = [coordState EXCEPT !.bcast = p]
  /\ UNCHANGED <<decision, pstate, alive, faulty, sentVote, forward>>

CoordDie ==
  /\ coordState.alive
  /\ coordState.alive' = FALSE
  /\ coordState' = [coordState EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED <<decision, pstate, sentVote, forward, alive, faulty>>

ParticipantSendVote(p) ==
  /\ alive[p]
  /\ ~sentVote[p]
  /\ decision' = [decision EXCEPT ![p] = no]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, alive, faulty, coordState, forward>>

ParticipantAbortVote(p) ==
  /\ coordState.alive
  /\ coordState.vote = yes
  /\ alive[p]
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = no]
  /\ UNCHANGED <<pstate, sentVote, coordState, alive, faulty, forward>>

\* Pre-decision from coordinator broadcast.
ParticipantPreDecideCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordState.bcast = p
  /\ forward[p][p] = notsent
  /\ forward' = [forward EXCEPT ![p][p] = IF coordState.decision = commit THEN commit ELSE abort]
  /\ UNCHANGED <<decision, pstate, alive, sentVote, coordState, faulty>>

\* Pre-decision from a peer's forwarding.
ParticipantPreDecideForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants : q # p /\ forward[q][p] # notsent /\ forward[p][p] = notsent
  /\ LET x == CHOOSE q \in participants : q # p /\ forward[q][p] # notsent IN
       forward' = [forward EXCEPT ![p][p] = forward[q][p]]
  /\ UNCHANGED <<decision, pstate, alive, sentVote, coordState, faulty>>

\* Forward a pre-decision to another participant.
ParticipantForward(p) ==
  /\ alive[p]
  /\ forward[p][p] # notsent
  /\ \E r \in participants :
       /\ r # p
       /\ forward[p][r] = notsent
       /\ forward' = [forward EXCEPT ![p][r] = forward[p][p]]
  /\ UNCHANGED <<decision, pstate, alive, sentVote, coordState, faulty>>

\* Only after forwarding to everyone does a non-faulty participant finalize.
ParticipantDecide(p) ==
  /\ alive[p]
  /\ pstate[p] = waiting
  /\ decision[p] # undecided
  /\ \A r \in participants : forward[p][r] = (IF decision[p] = yes THEN commit ELSE abort)
  /\ pstate' = [pstate EXCEPT ![p] = (IF decision[p] = yes THEN commit ELSE abort)]
  /\ UNCHANGED <<decision, alive, sentVote, coordState, forward, faulty>>

ParticipantAbortTimeout(p) ==
  /\ alive[p]
  /\ pstate[p] = waiting
  /\ ~coordState.alive
  /\ \A q \in participants : coordState.bcast # q
  /\ \A q \in participants : \A r \in participants : ~(~alive[q] /\ forward[q][r] # notsent)
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = no]
  /\ pstate' = [pstate EXCEPT ![p] = abort]
  /\ UNCHANGED <<sentVote, coordState, alive, forward, faulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<decision, pstate, sentVote, coordState, forward>>

CoordStep == CoordDecide \/ CoordDie

DecideStep(p) == ParticipantDecide(p) \/ ParticipantAbortTimeout(p)

DecideSteps == \E p \in participants : DecideStep(p)

ParticipantStep == DecideStep("p1") \/ ParticipantSendVote("p1") \/ ParticipantAbortVote("p1") \/ ParticipantPreDecideCoord("p1") \/ ParticipantPreDecideForward("p1") \/ ParticipantForward("p1") \/ ParticipantDie("p1")

Next ==
  \/ CoordStep
  \/ DecideSteps
  \/ ParticipantStep
  \/ \E p \in participants : CoordGetVote(p) \/ CoordDetectFault(p) \/ CoordBroadcast(p) \/ ParticipantSendVote(p) \/ ParticipantAbortVote(p) \/ ParticipantPreDecideCoord(p) \/ ParticipantPreDecideForward(p) \/ ParticipantForward(p) \/ ParticipantDecide(p) \/ ParticipantAbortTimeout(p) \/ ParticipantDie(p)

\* Fairness: coordinator and participant progress steps are weakly fair;
\* death steps (which are never guaranteed to fire) are left unfair.
SpecNB == Init /\ [][Next]_vars
  /\ WF_vars(DecideSteps) /\ WF_vars(ParticipantStep) /\ WF_vars(CoordStep)

TypeInvNB == TypeOK

\* Agreement: no two participants can reach different decisions.
Agreement ==
  \A p \in participants : \A q \in participants :
    (pstate[p] = commit /\ pstate[q] = abort) => FALSE

\* Non-blocking: every non-faulty participant eventually decides.
AllDecide == \A p \in participants : (alive[p] /\ pstate[p] = waiting) ~> (pstate[p] # waiting)

====
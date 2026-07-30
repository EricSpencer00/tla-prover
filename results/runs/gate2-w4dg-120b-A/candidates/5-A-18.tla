---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinator and participants send messages asynchronously; failure detection is
\* modeled as immediate (magical), not timeout-based. Simple broadcast means a
\* crashed coordinator can leave participants undecided, so AC5 (non-blocking
\* termination) does NOT hold -- only AC3's weaker liveness holds.

VARIABLES
  vote, alive, decision, faulty, sentVote,
  coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentVote,
           coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ sentVote \subseteq participants
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \subseteq {"coord"}

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ sentVote = {}
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = {}

\* Coordinator actions
SendVoteRequest(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                coordVote, coordSent, coordDecision, coordFaulty>>

RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordVote[p] = waiting
  /\ p \in sentVote
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                coordRequested, coordSent, coordDecision, coordAlive, coordFaulty>>

DetectParticipantFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                coordRequested, coordVote, coordSent, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordRequested[p] /\ coordVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                coordRequested, coordVote, coordSent, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                coordRequested, coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = {"coord"}
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                coordRequested, coordVote, coordSent, coordDecision>>

\* Participant actions
SendVote(p) ==
  /\ alive[p]
  /\ coordRequested[p]
  /\ p \notin sentVote
  /\ sentVote' = sentVote \cup {p}
  /\ UNCHANGED <<vote, alive, decision, faulty,
                coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortUnanimousNo(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ p \in sentVote
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnLostVoteRequest(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~coordRequested[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

DecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordSent[p] \in {commit, abort}
  /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, sentVote,
                coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : SendVoteRequest(p)
  \/ \E p \in participants : RecvVote(p)
  \/ \E p \in participants : DetectParticipantFault(p)
  \/ MakeDecision
  \/ \E p \in participants : BroadcastDecision(p)
  \/ CoordDie
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortUnanimousNo(p)
  \/ \E p \in participants : AbortOnLostVoteRequest(p)
  \/ \E p \in participants : DecideFromCoordinator(p)
  \/ \E p \in participants : ParticipantDie(p)

Spec == Init /\ [][Next]_vars
  /\ (\A p \in participants :
        WF_vars(SendVote(p)) /\ WF_vars(AbortUnanimousNo(p))
          /\ WF_vars(DecideFromCoordinator(p)))

\* Safety: agreement, commit/abort validity, and irrevocability.
AC1 == \A a, b \in participants :
        (decision[a] = commit /\ decision[b] = abort) => a = b

AC2 == \A a \in participants : decision[a] = commit => (\A b \in participants : vote[b] = yes)

AC3 == \A a \in participants : decision[a] = abort =>
       \/ \E b \in participants : vote[b] = no
       \/ faulty # {}
       \/ coordFaulty # {}

AC4 == \A a \in participants :
        /\ (decision[a] = commit => (\A m \in [participants -> {commit, abort}] : decision[a] = m))
        /\ (decision[a] = abort => (\A m \in [participants -> {commit, abort}] : decision[a] = m))

\* Liveness: the weakly non-blocking outcome -- not guaranteed for every live
\* participant (the simple broadcast variant can leave some undecided).
AC3 == <>(\A p \in participants : decision[p] # undecided \/ p \in faulty \/ coordFaulty # {})

====
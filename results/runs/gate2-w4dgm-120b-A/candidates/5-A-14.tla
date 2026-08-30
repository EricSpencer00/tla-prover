---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voted, coordState, coordAlive, coordFaulty

vars == <<pstate, alive, decision, faulty, voted, coordState, coordAlive, coordFaulty>>

TypeInv ==
  /\ pstate \in [participants -> {undecided, commit, abort}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in {undecided, commit, abort}
  /\ faulty \in [participants -> BOOLEAN]
  /\ voted \in [participants -> {waiting, yes, no}]
  /\ coordState \in [participants -> {notsent, commit, abort}]
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ pstate = [pa \in participants |-> undecided]
  /\ alive = [pa \in participants |-> TRUE]
  /\ decision = undecided
  /\ faulty = [pa \in participants |-> FALSE]
  /\ voted = [pa \in participants |-> CHOOSE v \in {yes, no} : TRUE]
  /\ coordState = [pa \in participants |-> notsent]
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator actions
SendRequest(pa) ==
  /\ coordAlive
  /\ coordState[pa] = notsent
  /\ coordState' = [coordState EXCEPT ![pa] = waiting]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, coordAlive, coordFaulty>>

RecvVote(pa) ==
  /\ coordAlive
  /\ decision = undecided
  /\ coordState[pa] = waiting
  /\ voted[pa] \in {yes, no}
  /\ coordState' = [coordState EXCEPT ![pa] = voted[pa]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, coordAlive, coordFaulty>>

DetectFault(pa) ==
  /\ coordAlive
  /\ decision = undecided
  /\ coordState[pa] = waiting
  /\ ~alive[pa]
  /\ coordState' = [coordState EXCEPT ![pa] = notsent]
  /\ decision' = abort
  /\ UNCHANGED <<pstate, alive, faulty, voted, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ decision = undecided
  /\ \A pa \in participants: coordState[pa] # waiting
  /\ decision' = IF \A pa \in participants: coordState[pa] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pstate, alive, faulty, voted, coordState, coordAlive, coordFaulty>>

Broadcast(pa) ==
  /\ coordAlive
  /\ decision # undecided
  /\ coordState[pa] = waiting \/ coordState[pa] = notsent
  /\ coordState' = [coordState EXCEPT ![pa] = decision]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, coordState>>

\* Participant actions
SendVote(pa) ==
  /\ alive[pa]
  /\ coordState[pa] = notsent
  /\ coordState' = [coordState EXCEPT ![pa] = waiting]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, coordAlive, coordFaulty>>

AbortOnVote(pa) ==
  /\ alive[pa]
  /\ pstate[pa] = undecided
  /\ voted[pa] = no
  /\ pstate' = [pstate EXCEPT ![pa] = abort]
  /\ UNCHANGED <<alive, decision, faulty, voted, coordState, coordAlive, coordFaulty>>

AbortOnTimeout(pa) ==
  /\ alive[pa]
  /\ pstate[pa] = undecided
  /\ coordState[pa] = notsent
  /\ coordFaulty
  /\ pstate' = [pstate EXCEPT ![pa] = abort]
  /\ UNCHANGED <<alive, decision, faulty, voted, coordState, coordAlive, coordFaulty>>

Decide(pa) ==
  /\ alive[pa]
  /\ pstate[pa] = undecided
  /\ coordState[pa] \in {commit, abort}
  /\ pstate' = [pstate EXCEPT ![pa] = coordState[pa]]
  /\ UNCHANGED <<alive, decision, faulty, voted, coordState, coordAlive, coordFaulty>>

ParticipantDie(pa) ==
  /\ alive[pa]
  /\ alive' = [alive EXCEPT ![pa] = FALSE]
  /\ faulty' = [faulty EXCEPT ![pa] = TRUE]
  /\ UNCHANGED <<pstate, decision, voted, coordState, coordAlive, coordFaulty>>

Next ==
  \/ \E pa \in participants: SendRequest(pa)
  \/ \E pa \in participants: RecvVote(pa)
  \/ \E pa \in participants: DetectFault(pa)
  \/ MakeDecision
  \/ \E pa \in participants: Broadcast(pa)
  \/ CoordDie
  \/ \E pa \in participants: SendVote(pa)
  \/ \E pa \in participants: AbortOnVote(pa)
  \/ \E pa \in participants: AbortOnTimeout(pa)
  \/ \E pa \in participants: Decide(pa)
  \/ \E pa \in participants: ParticipantDie(pa)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A pa \in participants: SF_vars(SendVote(pa))
  /\ \A pa \in participants: SF_vars(AbortOnVote(pa))
  /\ \A pa \in participants: SF_vars(Decide(pa))
  /\ SF_vars(MakeDecision)

\* Safety: no two participants decide differently, and any commit/abort is
\* backed by unanimous yes or by a no/failure, respectively.
Agreement ==
  \A pa, pb \in participants: (pstate[pa] = commit /\ pstate[pb] = abort) => FALSE
CommitValidity ==
  (\E pa \in participants: pstate[pa] = commit) => (\A pa \in participants: voted[pa] = yes)
AbortValidity ==
  (\E pa \in participants: pstate[pa] = abort) =>
    (\E pa \in participants: voted[pa] = no) \/ (\E pa \in participants: faulty[pa]) \/ coordFaulty
Irrevocability ==
  \A pa \in participants:
    /\ (pstate[pa] = commit) ~> (pstate[pa] = commit)
    /\ (pstate[pa] = abort) ~> (pstate[pa] = abort)

\* Liveness: the protocol eventually reaches a decision or a failure.
Termination ==
  <>(\A pa \in participants: pstate[pa] # undecided \/ faulty[pa] \/ coordFaulty)

====
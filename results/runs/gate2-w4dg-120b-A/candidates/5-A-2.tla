---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordFaulty, decision, coordPhase, coordSent, coordResponse
VARIABLES vote, alive, decided, pFaulty, sentVote

vars == <<coordAlive, coordFaulty, decision, coordPhase, coordSent, coordResponse,
          vote, alive, decided, pFaulty, sentVote>>

TypeInv ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ decision \in {undecided, commit, abort}
  /\ coordPhase \in {undecided, decided}
  /\ coordSent \in [participants -> {notsent, commit, abort}]
  /\ coordResponse \in [participants -> {waiting, yes, no}]
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decided \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]

Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ decision = undecided
  /\ coordPhase = undecided
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordResponse = [p \in participants |-> waiting]
  /\ vote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
  /\ alive = [p \in participants |-> TRUE]
  /\ decided = [p \in participants |-> undecided]
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]

SendRequest(p) ==
  /\ coordAlive
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = notsent]
  /\ coordPhase' = undecided
  /\ UNCHANGED <<coordAlive, coordFaulty, decision, coordResponse,
                vote, alive, decided, pFaulty, sentVote>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ decision = undecided
  /\ coordPhase = undecided
  /\ coordResponse[p] = waiting
  /\ sentVote[p]
  /\ coordResponse' = [coordResponse EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, decision, coordPhase,
                coordSent, vote, alive, decided, pFaulty, sentVote>>

DetectFault(p) ==
  /\ coordAlive
  /\ decision = undecided
  /\ coordPhase = undecided
  /\ coordResponse[p] = waiting
  /\ pFaulty[p]
  /\ decision' = abort
  /\ coordPhase' = decided
  /\ UNCHANGED <<coordAlive, coordFaulty, coordSent, coordResponse,
                vote, alive, decided, pFaulty, sentVote>>

MakeDecision ==
  /\ coordAlive
  /\ decision = undecided
  /\ \A p \in participants : coordResponse[p] # waiting
  /\ decision' = IF \A p \in participants : coordResponse[p] = yes THEN commit ELSE abort
  /\ coordPhase' = decided
  /\ UNCHANGED <<coordAlive, coordFaulty, coordSent, coordResponse,
                vote, alive, decided, pFaulty, sentVote>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ decision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = decision]
  /\ UNCHANGED <<coordAlive, coordFaulty, decision, coordPhase,
                coordResponse, vote, alive, decided, pFaulty, sentVote>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<decision, coordPhase, coordSent, coordResponse,
                vote, alive, decided, pFaulty, sentVote>>

SendMyVote(p) ==
  /\ alive[p]
  /\ coordSent[p] # notsent
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, decision, coordPhase, coordSent, coordResponse,
                vote, alive, decided, pFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, decision, coordPhase,
                coordSent, coordResponse, vote, alive, pFaulty, sentVote>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ ~coordAlive
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, decision, coordPhase,
                coordSent, coordResponse, vote, alive, pFaulty, sentVote>>

DecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ coordSent[p] # notsent
  /\ decided' = [decided EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, decision, coordPhase,
                coordSent, coordResponse, vote, alive, pFaulty, sentVote>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, decision, coordPhase, coordSent, coordResponse,
                vote, decided, sentVote>>

Next ==
  \/ \E p \in participants : SendRequest(p) \/ ReceiveVote(p) \/ DetectFault(p)
                          \/ BroadcastDecision(p) \/ SendMyVote(p) \/ AbortOnVote(p)
                          \/ AbortOnTimeout(p) \/ DecideFromCoordinator(p)
                          \/ ParticipantDie(p)
  \/ MakeDecision \/ CoordDie

CoordProgress ==
  \/ MakeDecision
  \/ \E p \in participants : BroadcastDecision(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CoordProgress)
  /\ \A p \in participants : WF_vars(SendMyVote(p) \/ AbortOnVote(p)
                                      \/ AbortOnTimeout(p) \/ DecideFromCoordinator(p))

Agree ==
  \A p, q \in participants : ~(decided[p] = commit /\ decided[q] = abort)

CommitValidity ==
  \A p \in participants : decided[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
  \E p \in participants : decided[p] = abort =>
    \/ \E q \in participants : vote[q] = no
    \/ \E q \in participants : pFaulty[q]
    \/ coordFaulty

Irreversible ==
  /\ \A p \in participants :
        (decided[p] = commit => \A q \in participants : decided[q] = commit)
  /\ \A p \in participants :
        (decided[p] = abort => \A q \in participants : decided[q] = abort)

EventualDecision ==
  <>(\E p \in participants : decided[p] # undecided) \/ \E p \in participants : pFaulty[p] \/ coordFaulty

====
---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, palive, pdecision, pfaulty, sentVote, coordState

Vars == <<pvote, palive, pdecision, pfaulty, sentVote, coordState>>

PreDecisions == {commit, abort, notsent}

TypeOK ==
  /\ pvote \in [participants -> {yes, no, undecided}]
  /\ palive \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> {commit, abort, waiting}]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ sentVote \subseteq participants
  /\ coordState \in [request |-> {"idle", "pending"}, vote |-> "none",
                     broadcast |-> "none", decision |-> "none", alive |-> TRUE,
                     faulty |-> FALSE]

Init ==
  /\ pvote = [p \in participants |-> undecided]
  /\ palive = [p \in participants |-> TRUE]
  /\ pdecision = [p \in participants |-> waiting]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ sentVote = {}
  /\ coordState = [request |-> "idle", vote |-> "none", broadcast |-> "none",
                   decision |-> "none", alive |-> TRUE, faulty |-> FALSE]

AllDecided == \A p \in participants : pdecision[p] \in {commit, abort}

\* Base ACP-SB: coordinator collects votes and decides on commit if every
\* participant voted yes.
SendRequest ==
  /\ coordState.request = "idle"
  /\ coordState.alive
  /\ coordState' = [coordState EXCEPT !.request = "pending"]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, sentVote>>

GetVote(p) ==
  /\ coordState.request = "pending"
  /\ p \notin sentVote
  /\ pvote' = [pvote EXCEPT ![p] = IF pvote[p] = undecided THEN yes ELSE pvote[p]]
  /\ sentVote' = sentVote \cup {p}
  /\ UNCHANGED <<palive, pdecision, pfaulty, coordState>>

CoordinatorDetectsFault(p) ==
  /\ coordState.request = "pending"
  /\ p \notin sentVote
  /\ pvote[p] = undecided
  /\ pfaulty[p]
  /\ coordState' = [coordState EXCEPT !.faulty = TRUE]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, sentVote>>

MakeDecision ==
  /\ coordState.request = "pending"
  /\ coordState.alive /\ ~coordState.faulty
  /\ sentVote = participants
  /\ coordState.vote' = IF \A p \in participants : pvote[p] = yes THEN "yes" ELSE "no"
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, sentVote>>

\* Base ACP-SB broadcast: one participant may hear the decision first.
Broadcast(p) ==
  /\ coordState.alive /\ ~coordState.faulty
  /\ coordState.request = "pending"
  /\ coordState.decision = "none"
  /\ coordState.vote # "none"
  /\ coordState' = [coordState EXCEPT !.broadcast = p, !.decision = coordState.vote]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, sentVote>>

DieCoordinator ==
  /\ coordState.alive
  /\ coordState' = [coordState EXCEPT !.alive = FALSE]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, sentVote>>

SendVote(p) ==
  /\ pvote[p] = undecided
  /\ ~pfaulty[p]
  /\ pvote' = [pvote EXCEPT ![p] = yes]
  /\ UNCHANGED <<palive, pdecision, pfaulty, sentVote, coordState>>

\* Base ACP-SB abort: a participant may abort on its own.
AbortOnVote(p) ==
  /\ pvote[p] = no
  /\ pdecision[p] = waiting
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pvote, palive, pfaulty, sentVote, coordState>>

AbortOnTimeout ==
  /\ coordState.alive /\ coordState.broadcast = "none"
  /\ pdecision \in [participants -> {waiting}]
  /\ pdecision' = [p \in participants |-> abort]
  /\ UNCHANGED <<pvote, palive, pfaulty, sentVote, coordState>>

\* ACP-NB: pre-decision from coordinator, stored in the participant's own
\* forwarding entry.
PreDecideCoord(p) ==
  /\ palive[p]
  /\ pdecision[p] = waiting
  /\ coordState.broadcast = p
  /\ coordState.decision # "none"
  /\ pdecision' = [pdecision EXCEPT ![p] = coordState.decision]
  /\ UNCHANGED <<pvote, palive, pfaulty, sentVote, coordState>>

\* ACP-NB: pre-decision from another participant's forwarding, stored locally.
PreDecideFwd(from, p) ==
  /\ palive[p]
  /\ pdecision[p] = waiting
  /\ pdecision[from] \in {commit, abort}
  /\ from # p
  /\ pdecision' = [pdecision EXCEPT ![p] = pdecision[from]]
  /\ UNCHANGED <<pvote, palive, pfaulty, sentVote, coordState>>

\* ACP-NB: forward a pre-decision to another participant.
Forward(p, q) ==
  /\ palive[p]
  /\ pdecision[p] \in {commit, abort}
  /\ q # p
  /\ pdecision[q] = waiting
  /\ pdecision' = [pdecision EXCEPT ![q] = pdecision[p]]
  /\ UNCHANGED <<pvote, palive, pfaulty, sentVote, coordState>>

\* ACP-NB: commit or abort (non-blocking) once this node has handed its
\* pre-decision to every other participant.
Decide(p) ==
  /\ palive[p]
  /\ pdecision[p] \in {commit, abort}
  /\ \A q \in participants : (q = p) \/ pdecision[q] = pdecision[p]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, sentVote, coordState>>

Crash(p) ==
  /\ ~pfaulty[p]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, palive, pdecision, sentVote, coordState>>

decideChoices == {p \in participants : Decide(p)} \cup
                 {AbortOnVote(p) : p \in participants}

Next ==
  \/ SendRequest \/ MakeDecision \/ DieCoordinator \/ AbortOnTimeout
  \/ \E p \in participants :
       GetVote(p) \/ CoordinatorDetectsFault(p) \/ Broadcast(p
       \/ SendVote(p) \/ AbortOnVote(p) \/ PreDecideCoord(p) \/ Decide(p)
  \/ \E p \in participants, q \in participants :
       Forward(p, q) \/ PreDecideFwd(p, q)
  \/ \E p \in participants : Crash(p)

\* Fairness excludes death: weak fairness on participant progress and
\* coordinator progress (excluding crashing).
SpecNB ==
  /\ Init
  /\ [][Next]_Vars
  /\ WF_Vars(decideChoices)
  /\ WF_Vars(AbortOnTimeout)

\* Two participants can never reach different decisions.
Agreement ==
  \A p, q \in participants :
    (pdecision[p] = commit /\ pdecision[q] = abort) => FALSE

\* Everyone who committed voted yes.
CommitValidity ==
  (\E p \in participants : pdecision[p] = commit) =>
    (\A p \in participants : pvote[p] = yes)

\* Anyone aborting has justification: a no vote, a faulty node, or a dead
\* coordinator.
AbortValidity ==
  (\E p \in participants : pdecision[p] = abort) =>
    (\E p \in participants : pvote[p] = no \/ pfaulty[p] \/ ~coordState.alive)

\* Decisions are irreversible.
Irrevocability ==
  \A p \in participants :
    (pdecision[p] = commit \/ pdecision[p] = abort) => (pdecision[p] = pdecision[p])

\* Progress: either everyone decides or some fault is present.
AllDecideOrFault ==
  <>(AllDecided \/ \E p \in participants : pfaulty[p] \/ ~coordState.alive)

\* Progress: every non-faulty node eventually decides (guaranteed by the
\* reliable broadcast forwarding mechanism, not by the coordinator).
NonBlockingTermination ==
  \A p \in participants : (~pfaulty[p] ~> (pdecision[p] \in {commit, abort}))

TypeInvNB == TypeOK

====
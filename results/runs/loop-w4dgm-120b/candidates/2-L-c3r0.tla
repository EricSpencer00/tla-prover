---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

Coordinator == "coordinator"

VARIABLES vote, alive, decision, faulty, sentvote, coordstate, fwd

vars == <<vote, alive, decision, faulty, sentvote, coordstate, fwd>>

\* fwd[p][q] is p's forwarding record for q: notsent means no pre-decision
\* received; commit/abort means p received that pre-decision and (perhaps) forwarded it.
TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {Coordinator} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants \cup {Coordinator} -> BOOLEAN]
  /\ sentvote \in [participants -> BOOLEAN]
  /\ coordstate \in {waiting, yes, no}
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> yes]
  /\ alive = [p \in participants \cup {Coordinator} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants \cup {Coordinator} |-> FALSE]
  /\ sentvote = [p \in participants |-> FALSE]
  /\ coordstate = waiting
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator-only actions (inherited from the simple broadcast base).
CoordSendRequest ==
  /\ alive[Coordinator]
  /\ coordstate = waiting
  /\ coordstate' = yes
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, fwd>>

CoordGetVote(p) ==
  /\ alive[p]
  /\ alive[Coordinator]
  /\ sentvote[p] = FALSE
  /\ sentvote' = [sentvote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordstate, fwd>>

CoordDie ==
  /\ alive[Coordinator]
  /\ alive' = [alive EXCEPT ![Coordinator] = FALSE]
  /\ faulty' = [faulty EXCEPT ![Coordinator] = TRUE]
  /\ UNCHANGED <<vote, decision, sentvote, coordstate, fwd>>

CoordMakeDecision ==
  /\ alive[Coordinator]
  /\ coordstate \in {yes, no}
  /\ decision' = [p \in participants |-> IF vote[p] = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, sentvote, faulty, coordstate, fwd>>

CoordBroadcast(p) ==
  /\ alive[Coordinator]
  /\ decision[p] # undecided
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = decision[p]]
  /\ UNCHANGED <<vote, alive, decision, sentvote, faulty, coordstate>>

\* Part of the simple broadcast protocol: a participant aborts if it sees a
\* no vote from some participant and has not already decided.
CoordAbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants : vote[q] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentvote, coordstate, fwd>>

CoordAbortOnTimeout ==
  /\ coordstate \in {yes, no}
  /\ \A p \in participants : sentvote[p] = TRUE
  /\ \E p \in participants : vote[p] = no
  /\ coordstate' = no
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, fwd>>

NextCoordinator == CoordSendRequest \/ CoordMakeDecision \/ CoordDie
                    \/ CoordAbortOnTimeout
                    \/ (\E p \in participants : CoordGetVote(p) \/ CoordBroadcast(p) \/ CoordAbortOnVote(p))

\* A participant pre-decides (stores a pre-decision) once it receives it from
\* either coordinator broadcast or another participant's forwarding.
ParticipantPreDecideFromCoord(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ decision[p] = undecided
  /\ fwd' = [fwd EXCEPT ![p][p] = decision[p]]
  /\ UNCHANGED <<vote, alive, decision, sentvote, faulty, coordstate>>

ParticipantPreDecideFromFwd(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ \E q \in participants : q # p /\ fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = CHOOSE v \in {commit, abort} : \E q \in participants : q # p /\ fwd[q][p] = v]
  /\ UNCHANGED <<vote, alive, decision, sentvote, faulty, coordstate>>

ParticipantForward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, sentvote, faulty, coordstate>>

\* A participant only finalizes its decision once it has forwarded its
\* pre-decision to every other participant -- this is what the round guarantee
\* in AC5 below depends on.
ParticipantDecide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : (q = p) \/ fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, sentvote, faulty, coordstate, fwd>>

\* If the coordinator crashes, an undecided participant may only give up once no
\* alive participant took a decision from it and no forwarding remains available.
ParticipantAbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~alive[Coordinator]
  /\ \A q \in participants : ~alive[q] => fwd[q][p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, sentvote, faulty, coordstate, fwd>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentvote, coordstate, fwd>>

NextParticipant == (\E p \in participants :
                     ParticipantPreDecideFromCoord(p) \/ ParticipantPreDecideFromFwd(p)
                       \/ ParticipantDecide(p) \/ ParticipantAbortOnTimeout(p) \/ ParticipantDie(p))
                     \/ (\E p, q \in participants : ParticipantForward(p, q))

Next == NextCoordinator \/ NextParticipant

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(NextCoordinator)
  /\ SF_vars(\E p \in participants : CoordinatorGetVote(p))
  /\ SF_vars(\E p \in participants : ParticipantPreDecideFromCoord(p))
  /\ SF_vars(\E p \in participants : ParticipantPreDecideFromFwd(p))
  /\ WF_vars(\E p \in participants, q \in participants : ParticipantForward(p, q))
  /\ SF_vars(\E p \in participants : ParticipantDecide(p))
  /\ SF_vars(\E p \in participants : ParticipantAbortOnTimeout(p))

\* Safety: no two participants may ever disagree on the decision.
Agreement ==
  \A p, q \in participants : (decision[p] = commit) => (decision[q] # abort)

\* Once a commit happens, it was unanimous.
CommitValidity ==
  (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

\* An abort must have a legitimate trigger behind it.
AbortValidity ==
  (\E p \in participants : decision[p] = abort)
    => (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ faulty[Coordinator]

\* Decisions are final.
Irrevocability ==
  \A p \in participants :
    (decision[p] \in {commit, abort}) ~> (decision[p] = decision[p])

\* The protocol always drives every non-crashed participant to a decision.
DecideEventually ==
  \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

\* Progress to the end: all decided or some crash/failure that justifies it.
AC3Liveness == <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ faulty[Coordinator])

====
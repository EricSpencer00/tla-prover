---- MODULE ACP_NB ----
EXTENDS Naturals

\* Non-blocking atomic commitment: the coordinator decides and broadcasts a
\* decision to all participants. Each participant forwards any decision it
\* receives to every other participant before finalizing its own. This
\* redundancy is what lets the protocol recover when the coordinator crashes
\* mid-broadcast, and is the reason every non-faulty participant can
\* eventually decide.
\* Participants and the coordinator may crash silently; the properties must
\* still hold in spite of that.
\* The spec extends the simple broadcast version (ACP-SB), reusing its
\* coordinator actions and adding the forwarding mechanism on top.

CONSTANTS participants, yes, no
CONSTANTS undecided, commit, abort
CONSTANTS waiting, notsent

VARIABLES vote, alive, decision, faulty
VARIABLES votesent, req, vresp, broadcasted, coordDecided
VARIABLES coordAlive, coordFaulty
VARIABLES fwd

vars == <<vote, alive, decision, faulty, votesent, req, vresp,
           broadcasted, coordDecided, coordAlive, coordFaulty, fwd>>

\* fwd[p][q] records what pre-decision participant p has sent to participant q,
\* or notsent if it has not forwarded anything to q yet.
\* fwd[p][p] records what pre-decision p has itself received (locally or by
\* forwarding from somebody else) but has not yet finalized.
\* Since participants forward to everyone, the finalization guard is that
\* p has reached out to all q \in participants, not just that p has some
\* entry set.

NoFwd == [q \in participants |-> notsent]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ votesent = [p \in participants |-> FALSE]
  /\ req = FALSE
  /\ vresp = 0
  /\ broadcasted = [p \in participants |-> FALSE]
  /\ coordDecided = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> NoFwd]

CoordinatorSendsRequest ==
  /\ coordAlive
  /\ ~req
  /\ req' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, vresp,
                 broadcasted, coordDecided, coordAlive, coordFaulty, fwd>>

ParticipantSendsYes(p) ==
  /\ alive[p]
  /\ vote[p] = undecided
  /\ ~votesent[p]
  /\ vote' = [vote EXCEPT ![p] = yes]
  /\ votesent' = [votesent EXCEPT ![p] = TRUE]
  /\ vresp' = vresp + 1
  /\ UNCHANGED <<alive, decision, faulty, req, broadcasted,
                 coordDecided, coordAlive, coordFaulty, fwd>>

ParticipantPreDecidesFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcasted[p]
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordDecided]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req,
                 vresp, broadcasted, coordDecided, coordAlive, coordFaulty>>

ParticipantPreDecidesFromPeer(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ \E q \in participants :
       /\ fwd[q][p] # notsent
       /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req,
                 vresp, broadcasted, coordDecided, coordAlive, coordFaulty>>

ParticipantForwards(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req,
                 vresp, broadcasted, coordDecided, coordAlive, coordFaulty>>

ParticipantDecides(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, votesent, req,
                 vresp, broadcasted, coordDecided, coordAlive, coordFaulty, fwd>>

CoordinatorDetectsFault ==
  /\ coordAlive
  /\ coordFaulty
  /\ coordAlive' = FALSE
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req,
                 vresp, broadcasted, coordDecided, coordFaulty, fwd>>

CoordinatorMakesDecision ==
  /\ coordAlive
  /\ req
  /\ coordDecided = undecided
  /\ \A p \in participants : vote[p] = yes
  /\ coordDecided' = commit
  /\ broadcasted' = [p \in participants |-> TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req,
                 vresp, coordAlive, coordFaulty, fwd>>

CoordinatorAborts ==
  /\ coordAlive
  /\ req
  /\ coordDecided = undecided
  /\ (\E p \in participants : vote[p] = no \/ faulty[p])
  /\ coordDecided' = abort
  /\ broadcasted' = [p \in participants |-> TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req,
                 vresp, coordAlive, coordFaulty, fwd>>

CoordinatorBroadcasts ==
  /\ coordAlive
  /\ coordDecided # undecided
  /\ \E p \in participants : ~broadcasted[p]
  /\ broadcasted' = [p \in participants |->
                      IF ~broadcasted[p] THEN TRUE ELSE broadcasted[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req,
                 vresp, coordDecided, coordAlive, coordFaulty, fwd>>

CoordinatorDies ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, votesent, req,
                 vresp, broadcasted, coordDecided, fwd>>

ParticipantAbortsOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : ~broadcasted[q]
  /\ \A d \in participants, e \in participants : fwd[d][e] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, votesent, req,
                 vresp, broadcasted, coordDecided, coordAlive, coordFaulty, fwd>>

ParticipantCrashes(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, votesent, req,
                 vresp, broadcasted, coordDecided,
                 coordAlive, coordFaulty, fwd>>

ParticipantProgress(p) ==
  \/ ParticipantPreDecidesFromCoordinator(p)
  \/ ParticipantPreDecidesFromPeer(p)
  \/ \E q \in participants : ParticipantForwards(p, q)
  \/ ParticipantDecides(p)
  \/ ParticipantAbortsOnTimeout(p)

Next ==
  \/ CoordinatorSendsRequest
  \/ \E p \in participants : ParticipantSendsYes(p)
  \/ \E p \in participants : ParticipantProgress(p)
  \/ ParticipantCrashes(p)
  \/ CoordinatorDetectsFault
  \/ CoordinatorMakesDecision
  \/ CoordinatorAborts
  \/ CoordinatorBroadcasts
  \/ CoordinatorDies

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : ParticipantProgress(p))

TypeInvNB ==
  /\ vote \in [participants -> {undecided, yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ votesent \in [participants -> BOOLEAN]
  /\ req \in BOOLEAN
  /\ vresp \in 0..Cardinality(participants)
  /\ broadcasted \in [participants -> BOOLEAN]
  /\ coordDecided \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* Safety: the coordinator's all-or-nothing rule holds even under silent
\* crashes, and delivered decisions are immutable.
Agreement ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValidity ==
  \A p \in participants : decision[p] = commit =>
    \A q \in participants : vote[q] = yes

AbortValidity ==
  \A p \in participants : decision[p] = abort =>
    (\E q \in participants : vote[q] = no \/ faulty[q]) \/ coordFaulty

Irreversibility ==
  \A p \in participants :
    (decision[p] \in {commit, abort}) ~>
      (decision[p] = decision[p])

\* Liveness: every non-faulty participant eventually decides, a property
\* the simple broadcast variant fails to guarantee after a coordinator crash.
EventualDecision ==
  \A p \in participants : alive[p] ~> (decision[p] # undecided)

====
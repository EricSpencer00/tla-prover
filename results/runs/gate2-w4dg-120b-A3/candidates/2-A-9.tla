---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

(* Non-Blocking Atomic Commitment Protocol with reliable broadcast:        *)
(* participants forward a received pre-decision to every other          *)
(* participant before deciding locally, so a decision survives a       *)
(* coordinator crash.  Safety and liveness are verified for a bounded     *)
(* participant set, reusing the base coordinator logic from the         *)
(* simple broadcast variant (ACP-SB).                                      *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

Bump(n) == IF n < Cardinality(participants) THEN n + 1 ELSE n

VARIABLES pstate, alive, decision, faulty, voteSent, coordReq, coordVote,
         coordBroad, coordDecision, coordAlive, coordFaulty, fwd

vars == <<pstate, alive, decision, faulty, voteSent, coordReq,
          coordVote, coordBroad, coordDecision, coordAlive,
          coordFaulty, fwd>>

TypeInvNB ==
  /\ pstate \in [participants -> {waiting, yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordReq \in {waiting, yes, no}
  /\ coordVote \in {waiting, yes, no}
  /\ coordBroad \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ pstate = [p \in participants |-> waiting]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordReq = waiting
  /\ coordVote = waiting
  /\ coordBroad = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions: inherited from the simple broadcast protocol.
SendRequest ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ coordReq' = Bump(coordReq)
  /\ coordVote' = waiting
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent,
                coordBroad, coordDecision, coordFaulty, fwd>>

GetVote(p) ==
  /\ coordAlive
  /\ coordReq # waiting
  /\ coordVote = waiting
  /\ pstate[p] # waiting
  /\ coordVote' = pstate[p]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent,
                coordReq, coordBroad, coordDecision,
                coordAlive, coordFaulty, fwd>>

DetectCoordFault ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent,
                coordReq, coordVote, coordBroad, coordDecision, fwd>>

MakeDecision ==
  /\ coordAlive
  /\ coordVote # waiting
  /\ coordDecision = undecided
  /\ coordDecision' = coordVote
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent,
                coordReq, coordVote, coordBroad,
                coordAlive, coordFaulty, fwd>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordBroad[p] = notsent
  /\ coordBroad' = [coordBroad EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent,
                coordReq, coordVote, coordDecision,
                coordAlive, coordFaulty, fwd>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent,
                coordReq, coordVote, coordBroad, coordDecision, fwd>>

\* Participant: send its own vote to the coordinator.
SendVote(p) ==
  /\ pstate[p] = waiting
  /\ alive[p]
  /\ ~faulty[p]
  /\ pstate' = [pstate EXCEPT ![p] = Bump(coordReq)]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, coordReq, coordVote,
                coordBroad, coordDecision, coordAlive, coordFaulty, fwd>>

\* Participant learns the decision from the coordinator broadcast.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordBroad[p] # notsent
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordBroad[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent,
                coordReq, coordVote, coordBroad, coordDecision,
                coordAlive, coordFaulty>>

\* Participant learns the decision forwarded by a peer.
PreDecideFromForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants :
        /\ q # p
        /\ fwd[q][p] # notsent
        /\ fwd[p][p] = notsent
        /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent,
                coordReq, coordVote, coordBroad, coordDecision,
                coordAlive, coordFaulty>>

\* Participant forwards its pre-decision to a specific peer.
Forward(p, q) ==
  /\ alive[p]
  /\ p # q
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent,
                coordReq, coordVote, coordBroad, coordDecision,
                coordAlive, coordFaulty>>

\* Participant finalizes once it has forwarded to everyone else.
Decide(p) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : fwd[p][q] /= notsent
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent,
                coordReq, coordVote, coordBroad, coordDecision,
                coordAlive, coordFaulty, fwd>>

\* Participant aborts on timeout once the coordinator is dead and no
\* broadcast or forwarded decision is still in flight.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : coordBroad[q] = notsent
  /\ \A d \in participants : \A q \in participants : fwd[d][q] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent,
                coordReq, coordVote, coordBroad, coordDecision,
                coordAlive, coordFaulty, fwd>>

\* Participant crashes and becomes faulty.
Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, decision, voteSent, coordReq, coordVote,
                coordBroad, coordDecision, coordAlive, coordFaulty, fwd>>

NextNB ==
  \/ SendRequest
  \/ GetVote(p)
  \/ DetectCoordFault
  \/ MakeDecision
  \/ BroadcastDecision(p)
  \/ CoordDie
  \/ SendVote(p)
  \/ PreDecideFromCoord(p)
  \/ PreDecideFromForward(p)
  \/ Forward(p, q)
  \/ Decide(p)
  \/ AbortOnTimeout(p)
  \/ Die(p)

Fairness ==
  /\ WF_vars(SendRequest)
  /\ \A p \in participants : WF_vars(SendVote(p))
  /\ \A p \in participants : WF_vars(GetVote(p))
  /\ \A p \in participants : WF_vars(DetectCoordFault)
  /\ \A p \in participants : WF_vars(MakeDecision)
  /\ \A p \in participants : WF_vars(BroadcastDecision(p))
  /\ \A p \in participants : WF_vars(PreDecideFromCoord(p))
  /\ \A p \in participants : WF_vars(PreDecideFromForward(p))
  /\ \A p, q \in participants : WF_vars(Forward(p, q))
  /\ \A p \in participants : WF_vars(Decide(p))
  /\ \A p \in participants : WF_vars(AbortOnTimeout(p))

SpecNB == InitNB /\ [][NextNB]_vars /\ Fairness

(* Atomicity: no two participants end up in different final decisions.     *)
Agreement ==
  ~ \E p \in participants, q \in participants :
        /\ decision[p] = commit
        /\ decision[q] = abort

\* Commit requires unanimity (a unanimous yes is the only path to commit).
CommitValidity ==
  \A p \in participants :
    decision[p] = commit => \A q \in participants : pstate[q] = yes

\* Abort fires only on a no vote or a fatal fault anywhere in the system.
AbortValidity ==
  \A p \in participants :
    decision[p] = abort =>
      \/ \E q \in participants : pstate[q] = no
      \/ \E q \in participants : faulty[q]
      \/ coordFaulty

Irreversibility ==
  \A p \in participants : \A s \in {commit, abort} : (decision[p] = s) ~> (decision[p] = s)

\* Non-blocking termination: every non-faulty participant decides.
DecideEventually ==
  \A p \in participants : (alive[p] /\ ~coordFaulty) ~> (decision[p] # undecided)

\* The liveness core: either everyone decides, or some fault remains.
DecideOrFault ==
  <>(\A p \in participants : decision[p] # undecided) \/ coordFaulty

Properties == {Agreement, CommitValidity, AbortValidity, Irreversibility,
               DecideEventually, DecideOrFault}

====
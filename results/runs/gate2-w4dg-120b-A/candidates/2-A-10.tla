---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

\* Non-Blocking Atomic Commitment (ACP-NB) with reliable broadcast forwarding.
\* Every participant forwards a received pre-decision to all others before
\* finalizing; this guarantees that a surviving participant can still learn
\* the decision even if the coordinator crashes mid-broadcast.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voteSent, coordReq, coordVote,
         coordBcast, coordDecision, coordAlive, coordFaulty, fwd

vars == << vote, alive, decision, faulty, voteSent, coordReq, coordVote,
           coordBcast, coordDecision, coordAlive, coordFaulty, fwd >>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, waiting}]
  /\ faulty \subseteq participants
  /\ voteSent \subseteq participants
  /\ coordReq \in {yes, no, undecided}
  /\ coordVote \in {yes, no, undecided}
  /\ coordBcast \subseteq participants
  /\ coordDecision \in {commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = {}
  /\ voteSent = {}
  /\ coordReq = undecided
  /\ coordVote = undecided
  /\ coordBcast = {}
  /\ coordDecision = abort
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator sends the collective request to all participants.
CoordinatorSendsRequest ==
  /\ coordAlive
  /\ coordReq = undecided
  /\ coordReq' = yes
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent, coordVote,
                 coordBcast, coordDecision, coordAlive, coordFaulty, fwd >>

\* A participant sends its vote back to the coordinator.
SendVote(p) ==
  /\ alive[p]
  /\ p \notin voteSent
  /\ vote[p] = undecided
  /\ vote' = [vote EXCEPT ![p] = coordReq]
  /\ voteSent' = voteSent \cup {p}
  /\ UNCHANGED << alive, decision, faulty, coordReq, coordVote, coordBcast,
                 coordDecision, coordAlive, coordFaulty, fwd >>

\* The coordinator detects that all votes have been collected.
DetectCoordFault ==
  /\ coordAlive
  /\ voteSent = participants
  /\ coordVote' = IF \A p \in participants : vote[p] = yes THEN yes ELSE no
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent, coordReq,
                 coordBcast, coordDecision, coordAlive, coordFaulty, fwd >>

\* The coordinator decides commit if all voted yes, abort otherwise.
DecideCoord ==
  /\ coordAlive
  /\ coordVote # undecided
  /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent, coordReq,
                 coordVote, coordBcast, coordAlive, coordFaulty, fwd >>

\* Coordinator broadcasts its decision to a participant.
BroadcastCoord(p) ==
  /\ coordAlive
  /\ coordBcast' = coordBcast \cup {p}
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent, coordReq,
                 coordVote, coordDecision, coordAlive, coordFaulty, fwd >>

\* A participant pre-decides on the coordinator's broadcast.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ p \in coordBcast
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent, coordReq,
                 coordVote, coordBcast, coordDecision, coordAlive,
                 coordFaulty >>

\* A participant pre-decides on a forwarded decision from another participant.
PreDecideFromFwd(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ fwd[p][p] = notsent
  /\ \E q \in participants :
       /\ q # p
       /\ fwd[q][p] # notsent
       /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent, coordReq,
                 coordVote, coordBcast, coordDecision, coordAlive,
                 coordFaulty >>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent, coordReq,
                 coordVote, coordBcast, coordDecision, coordAlive,
                 coordFaulty >>

\* Once a participant has forwarded to all others, it finalizes its decision.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ fwd[p][p] # notsent
  /\ \A q \in participants \ {p} : fwd[p][q] = fwd[p][p]
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED << vote, alive, faulty, voteSent, coordReq, coordVote,
                 coordBcast, coordDecision, coordAlive, coordFaulty, fwd >>

\* A participant aborts on timeout once the coordinator is dead and no
\* actionable broadcast or forward is available from any alive participant.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ ~coordAlive
  /\ \A q \in participants : q \notin coordBcast
  /\ \A q \in participants : \A r \in participants : fwd[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty, voteSent, coordReq, coordVote,
                 coordBcast, coordDecision, coordAlive, coordFaulty, fwd >>

\* Any participant may crash silently.
Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED << vote, decision, voteSent, coordReq, coordVote,
                 coordBcast, coordDecision, coordAlive, coordFaulty, fwd >>

\* A participant may crash silently while the coordinator is alive.
DieWhileCoordAlive ==
  /\ coordAlive
  /\ \E p \in participants : Die(p)
  /\ UNCHANGED << vote, decision, voteSent, coordReq, coordVote,
                 coordBcast, coordDecision, coordAlive, coordFaulty, fwd >>

\* The coordinator may crash silently.
DieCoord ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << vote, decision, faulty, voteSent, coordReq, coordVote,
                 coordBcast, coordDecision, alive, fwd >>

Next ==
  \/ CoordinatorSendsRequest
  \/ DetectCoordFault
  \/ DecideCoord
  \/ DieWhileCoordAlive
  \/ DieCoord
  \/ \E p \in participants :
       \/ SendVote(p)
       \/ PreDecideFromCoord(p)
       \/ PreDecideFromFwd(p)
       \/ Decide(p)
       \/ AbortOnTimeout(p)
       \/ \E q \in participants : Forward(p, q)
  \/ \E p \in participants : \E q \in participants \ {p} : Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_vars(DecideCoord)
  /\ SF_vars(Decide)
  /\ SF_vars(\E p \in participants : SendVote(p))
  /\ SF_vars(\E p \in participants : Die(p))
  /\ WF_vars(DieCoord)
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideFromFwd(p))
  /\ WF_vars(\E p \in participants : \E q \in participants : Forward(p, q))

\* Safety: no two participants ever end up with conflicting decisions.
AC1 == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)

\* Safety: commit only if every participant voted yes.
AC2 == (\E p \in participants : decision[p] = commit) =>
       (\A q \in participants : vote[q] = yes)

\* Safety: abort only if some participant voted no or some participant is faulty.
AC3 == (\E p \in participants : decision[p] = abort) =>
       (coordFaulty \/ faulty # {} \/ \E q \in participants : vote[q] = no)

\* Safety: decisions are irrevocable.
AC4 == \A p \in participants : (decision[p] = waiting) ~> (decision[p] # waiting)

\* Liveness: either everyone decides, or some participant or the coordinator fails.
AC3Live == <>(\A p \in participants : decision[p] # waiting \/ faulty # {} \/ coordFaulty)

\* Liveness: every non-faulty participant eventually decides (new in ACP-NB).
AC5 == \A p \in participants : (~coordFaulty /\ p \notin faulty) ~> (decision[p] # waiting)

Properties == AC1 /\ AC2 /\ AC3 /\ AC4 /\ AC3Live /\ AC5

====
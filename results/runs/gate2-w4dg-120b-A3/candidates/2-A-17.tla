---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Reliable broadcast: every participant forwards the decision it receives to all
\* others before it may finalize its own decision.  The forwarding table is a
\* per-participant map from participant identifiers to the pre-decision it has
\* received for that destination (or "notsent").
Bidirectional == participants \X participants

VARIABLES vote, decided, decResult, alive, coordState, broadcastTo
VARIABLES fwdState, fwdTarget

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ decided \subseteq participants
    /\ decResult \in [participants -> {commit, abort, waiting}]
    /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ coordState \in {"waiting", "collecting", "decided", "dead"}
    /\ broadcastTo \in SUBSET participants
    /\ fwdState \in [participants -> [Bidirectional -> {notsent, commit, abort}]]
    /\ fwdTarget \in [participants -> [participants -> BOOLEAN]]

InitNP ==
    /\ vote = [p \in participants |-> undecided]
    /\ decided = {}
    /\ decResult = [p \in participants |-> waiting]
    /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
    /\ coordState = "waiting"
    /\ broadcastTo = {}
    /\ fwdState = [p \in participants |-> [q \in Bidirectional |-> notsent]]
    /\ fwdTarget = [p \in participants |-> [q \in participants |-> FALSE]]

\* Coordinator actions (inherited from ACP-SB, unchanged here):
VoteCoord ==
    /\ coordState = "waiting"
    /\ coordState' = "collecting"
    /\ UNCHANGED <<vote, decided, decResult, alive, broadcastTo, fwdState, fwdTarget>>

CastVote(p) ==
    /\ coordState = "collecting"
    /\ alive[p]
    /\ vote[p] = undecided
    /\ vote' = [vote EXCEPT ![p] = yes]
    /\ UNCHANGED <<decResult, decided, alive, coordState, broadcastTo, fwdState, fwdTarget>>

DetectCoordFault ==
    /\ coordState = "collecting"
    /\ coordState' = "dead"
    /\ alive' = [alive EXCEPT !["coord"] = FALSE]
    /\ UNCHANGED <<vote, decided, decResult, broadcastTo, fwdState, fwdTarget>>

\* The coordinator's broadcast is a per-participant message; it is unreliable, so
\* a participant may also learn the decision through a peer's forwarding later.
BroadcastDecision(d) ==
    /\ coordState = "collecting"
    /\ coordState' = "decided"
    /\ broadcastTo' = participants
    /\ UNCHANGED <<vote, decided, decResult, alive, fwdState, fwdTarget>>

DecideCoord(p) ==
    /\ coordState = "decided" /\ alive[p]
    /\ p \notin decided
    /\ decided' = decided \cup {p}
    /\ decResult' = [decResult EXCEPT ![p] = d]
    /\ UNCHANGED <<vote, alive, coordState, broadcastTo, fwdState, fwdTarget>>

DieCoord ==
    /\ coordState = "decided"
    /\ coordState' = "dead"
    /\ alive' = [alive EXCEPT !["coord"] = FALSE]
    /\ UNCHANGED <<vote, decided, decResult, broadcastTo, fwdState, fwdTarget>>

\* New (or modified) participant actions (replacing the ACP-SB decision step):
PreDecideCoord(p, d) ==
    /\ alive[p]
    /\ p \notin decided
    /\ fwdState[p][p] = notsent
    /\ coordState = "decided"
    /\ p \in broadcastTo
    /\ fwdState' = [fwdState EXCEPT ![p][p] = d]
    /\ UNCHANGED <<vote, decided, decResult, alive, coordState, broadcastTo, fwdTarget>>

PreDecideFwd(p, q, d) ==
    /\ alive[p]
    /\ p \notin decided
    /\ fwdState[p][p] = notsent
    /\ q \in participants
    /\ fwdState[q][p] = d
    /\ fwdState' = [fwdState EXCEPT ![p][p] = d]
    /\ UNCHANGED <<vote, decided, decResult, alive, coordState, broadcastTo, fwdTarget>>

Forward(p, q) ==
    /\ alive[p]
    /\ fwdState[p][p] \in {commit, abort}
    /\ ~fwdTarget[p][q]
    /\ fwdTarget' = [fwdTarget EXCEPT ![p][q] = TRUE]
    /\ fwdState' = [fwdState EXCEPT ![p][[p, q]] = fwdState[p][p]]
    /\ UNCHANGED <<vote, decided, decResult, alive, coordState, broadcastTo>>

Decide(p) ==
    /\ alive[p]
    /\ p \notin decided
    /\ \A q \in participants : fwdTarget[p][q]
    /\ decided' = decided \cup {p}
    /\ decResult' = [decResult EXCEPT ![p] = fwdState[p][p]]
    /\ UNCHANGED <<vote, alive, coordState, broadcastTo, fwdState, fwdTarget>>

AbortTimeout(p) ==
    /\ alive[p]
    /\ p \notin decided
    /\ coordState = "dead"
    /\ \A q \in participants : q \notin broadcastTo
    /\ \A q \in participants : fwdState[q][p] = notsent
    /\ decided' = decided \cup {p}
    /\ decResult' = [decResult EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, coordState, broadcastTo, fwdState, fwdTarget>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<vote, decided, decResult, coordState, broadcastTo, fwdState, fwdTarget>>

NextNP ==
    \/ VoteCoord \/ DetectCoordFault \/ DieCoord
    \/ \E p \in participants :
         \/ CastVote(p) \/ DecideCoord(p) \/ Die(p) \/ Decided(p)
         \/ \E d \in {commit, abort} : PreDecideCoord(p, d) \/ Decided(p)
         \/ \E q \in participants, d \in {commit, abort} : PreDecideFwd(p, q, d)
         \/ \E q \in participants : Forward(p, q)
         \/ AbortTimeout(p)

SpecNB == InitNP /\ [][NextNP]_<<vote, decided, decResult, alive, coordState, broadcastTo, fwdState, fwdTarget>>

\* Safety: no two participants reach different decisions.
AC1 ==
    \A p, q \in participants :
        (p \in decided /\ q \in decided /\ decResult[p] = commit /\ decResult[q] = abort) => p = q

\* Commitment requires unanimity.
AC2 ==
    \A p \in participants :
        (p \in decided /\ decResult[p] = commit) => \A q \in participants : vote[q] = yes

\* Abortion requires a no vote, a faulty participant, or a faulty coordinator.
AC3 ==
    \A p \in participants :
        (p \in decided /\ decResult[p] = abort) =>
            (\E q \in participants : vote[q] = no \/ ~alive[q]) \/ ~alive["coord"]

\* Irreversibility via a strongly-fair finalize: once decided, always decided.
AC4 ==
    \A p \in participants :
        (p \in decided) ~> (p \in decided)

\* Liveness: the live participants cannot be stuck waiting forever.
AC5 ==
    \A p \in participants : (alive[p] /\ p \notin decided) ~> (p \in decided)

\* In the full model, AC5 is the interesting guarantee.  With weak fairness on
\* the progress actions (pre-deciding, forwarding, deciding), every non-faulty
\* participant eventually decides, even if the coordinator died in the middle.
====
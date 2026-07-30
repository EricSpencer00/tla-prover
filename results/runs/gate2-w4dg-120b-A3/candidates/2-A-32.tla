---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voted, coordstate, forward

vars == <<pstate, alive, decision, faulty, voted, coordstate, forward>>

PState == {"voting", "decided", "aborted"}
CoordState == {"idle", "requesting", "voting", "broadcasting", "decided", "dead"}
FwdStatus == {notsent, commit, abort}

RECURSIVE EmptyForward(_, _)
EmptyForward(f, S) ==
    IF S = {} THEN TRUE
    ELSE LET p == CHOOSE x \in S : TRUE
         IN /\ f[p] = notsent
            /\ EmptyForward(f, S \ {p})

Init ==
    /\ pstate = [p \in participants |-> "voting"]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = undecided
    /\ faulty = [p \in participants |-> FALSE]
    /\ voted = [p \in participants |-> undecided]
    /\ coordstate = "idle"
    /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

Request ==
    /\ coordstate = "idle"
    /\ coordstate' = "requesting"
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, forward>>

CastVote(p) ==
    /\ coordstate = "requesting"
    /\ alive[p]
    /\ voted[p] = undecided
    /\ \E v \in {yes, no} : voted' = [voted EXCEPT ![p] = v]
    /\ coordstate' = "voting"
    /\ UNCHANGED <<pstate, alive, decision, faulty, forward>>

DetectFault(p) ==
    /\ coordstate = "voting"
    /\ alive[p]
    /\ coordstate' = "requesting"
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, forward>>

DecideCoord(v) ==
    /\ coordstate = "voting"
    /\ \A p \in participants : alive[p] => voted[p] # undecided
    /\ decision' = v
    /\ coordstate' = "broadcasting"
    /\ UNCHANGED <<pstate, alive, faulty, voted, forward>>

DiedCoord ==
    /\ coordstate \in {"requesting", "voting"}
    /\ coordstate' = "dead"
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, forward>>

CastBroadcast(p) ==
    /\ decision # undecided
    /\ decision # waiting
    /\ coordstate = "broadcasting"
    /\ pstate[p] = "voting"
    /\ pstate' = [pstate EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<alive, decision, faulty, voted, coordstate, forward>>

PredecideFromCoordinator(p) ==
    /\ alive[p]
    /\ pstate[p] = "voting"
    /\ decision # undecided
    /\ decision # waiting
    /\ forward[p][p] = notsent
    /\ forward' = [forward EXCEPT ![p][p] = decision]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, coordstate>>

PredecideFromForwarding(p) ==
    /\ alive[p]
    /\ pstate[p] = "voting"
    /\ forward[p][p] = notsent
    /\ \E q \in participants :
         /\ forward[q][p] # notsent
         /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, coordstate>>

Forward(p, q) ==
    /\ alive[p]
    /\ forward[p][p] # notsent
    /\ forward[p][q] = notsent
    /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
    /\ UNCHANGED <<pstate, alive, decision, faulty, voted, coordstate>>

Decide(p) ==
    /\ alive[p]
    /\ pstate[p] = "decided"
    /\ forward' = [forward EXCEPT ![p] = [q \in participants |-> IF q = p THEN forward[p][p] ELSE commit]]
    /\ pstate' = [pstate EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<alive, decision, faulty, voted, coordstate>>

AbortCrash(p) ==
    /\ alive[p]
    /\ pstate[p] = "voting"
    /\ coordstate = "dead"
    /\ \A q \in participants : ~(alive[q] /\ forward[q][p] # notsent)
    /\ \A q \in participants : ~(~alive[q] /\ \E r \in participants : forward[q][r] # notsent)
    /\ pstate' = [pstate EXCEPT ![p] = "aborted"]
    /\ UNCHANGED <<alive, decision, faulty, voted, coordstate, forward>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pstate, decision, voted, coordstate, forward>>

Next ==
    \/ Request
    \/ DiedCoord
    \/ \E p \in participants :
         \/ CastVote(p)
         \/ DetectFault(p)
         \/ CastBroadcast(p)
         \/ PredecideFromCoordinator(p)
         \/ PredecideFromForwarding(p)
         \/ Decide(p)
         \/ AbortCrash(p)
         \/ Die(p)
    \/ \E v \in {commit, abort} : DecideCoord(v)
    \/ \E p, q \in participants : Forward(p, q)

SpecNB == Init /\ [][Next]_vars
        /\ WF_vars(Request) /\ WF_vars(DiedCoord)

TypeInvNB ==
    /\ pstate \in [participants -> PState]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in {undecided, commit, abort, waiting}
    /\ faulty \in [participants -> BOOLEAN]
    /\ voted \in [participants -> {undecided, yes, no}]
    /\ coordstate \in CoordState
    /\ forward \in [participants -> [participants -> FwdStatus]]

AC1 == \A p, q \in participants : ~(pstate[p] = "committed" /\ pstate[q] = "aborted")
AC2 == (\E p \in participants : pstate[p] = "committed") => \A p \in participants : voted[p] = yes
AC3 == (\E p \in participants : pstate[p] = "aborted") => (\E p \in participants : voted[p] = no) \/ (\E p \in participants : faulty[p]) \/ coordstate = "dead"
AC4 == \A p \in participants : (pstate[p] = "committed" \/ pstate[p] = "aborted") ~> (pstate[p] = "committed" \/ pstate[p] = "aborted")
AC5 == \A p \in participants : (alive[p] /\ pstate[p] = "voting") ~> (pstate[p] = "decided" \/ pstate[p] = "aborted")

====